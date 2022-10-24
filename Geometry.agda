module Geometry where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Data.Product
open import Data.List
open import Data.Rational as ℚ using (ℚ; NonNegative; 0ℚ; ∣_∣; _+_; -_; _-_; _<_; _≤_)
open import Data.Rational.Properties as ℚ using (≤-refl; +-monoˡ-<; ≤-reflexive; +-mono-<-≤; positive⁻¹; +-identityˡ; +-inverseˡ; +-comm)
open import Function.Base
open import Data.Integer as ℤ using (ℤ)
open import Data.Empty using (⊥)
open import Data.Product
open import Data.Sum
open import Data.Nat as ℕ using (ℕ)
open import Relation.Nullary
open import Agda.Builtin.Unit using (tt)
open import Data.Bool.Base using (Bool; true; false; T)
open import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary

record Point : Set where
    constructor newPoint
    field
        pointId : ℕ

record LineSegment : Set where
    constructor lineSeg
    field
        from : Point
        to : Point
        lineLength : ℚ
        nonNegative : NonNegative lineLength

zero-line-segment : (Point) → LineSegment
zero-line-segment p = lineSeg p p 0ℚ tt

line-sym : (LineSegment) → LineSegment
line-sym ls = lineSeg (LineSegment.to ls) (LineSegment.from ls) (LineSegment.lineLength ls) (LineSegment.nonNegative ls)

record Circle : Set where
    constructor circle
    field
        center : Point
        radius : ℚ
        nonNegative : NonNegative radius
        
radius-line-segment : (pointId : ℕ) → (Circle) → LineSegment
radius-line-segment pointId c = lineSeg (Circle.center c) (newPoint pointId) (Circle.radius c) (Circle.nonNegative c)

data PointEq (x : Point) : Point → Set where
  refl : PointEq x x

circle-intersection : (c1 c2 : Circle) 
    → (connectMidLine : LineSegment)
    → (PointEq (Circle.center c1) (LineSegment.from connectMidLine)) 
    → (PointEq (Circle.center c2) (LineSegment.to connectMidLine))
    → .{
        (LineSegment.lineLength connectMidLine) <
        (Circle.radius c1) + 
        (Circle.radius c2)
    }
    → .{
        ∣ (Circle.radius c1) - (Circle.radius c2) ∣ < (LineSegment.lineLength connectMidLine)
    }
    → (Σ (Point × Point) (λ (p1 , p2) →
        (LineSegment × LineSegment) × (LineSegment × LineSegment)
    ))

circle-intersection c1 c2 connectMidLine c1Mid c2Mid = 
    let p0 = newPoint 0
        p1 = newPoint 1
    in (p0 , p1) , (
        ((lineSeg (Circle.center c1) p0 (Circle.radius c1) (Circle.nonNegative c1)) , 
         (lineSeg (Circle.center c2) p0 (Circle.radius c2)) (Circle.nonNegative c2)), 
        ((lineSeg (Circle.center c1) p1 (Circle.radius c1) (Circle.nonNegative c1)) , 
         (lineSeg (Circle.center c2) p1 (Circle.radius c2)) (Circle.nonNegative c2))
    )

record Triangle : Set where
  constructor from-edges
  field
    edge0 : LineSegment
    edge1 : LineSegment
    edge2 : LineSegment
    .edgesConnected : 
        (PointEq (LineSegment.to edge0) (LineSegment.from edge1)) ×
        (PointEq (LineSegment.to edge1) (LineSegment.from edge2)) ×
        (PointEq (LineSegment.to edge2) (LineSegment.from edge0))

is-equilateral : (t : Triangle) → Set
is-equilateral (from-edges edge0 edge1 edge2 _) = 
    (LineSegment.lineLength edge0 ℚ.≃ LineSegment.lineLength edge1) ×
     (LineSegment.lineLength edge0 ℚ.≃ LineSegment.lineLength edge2)

x<x+x : (x : ℚ) → 0ℚ < x → (x < x + x)
x<x+x x p = (begin-strict
        x       ≡⟨ (sym ∘ +-identityˡ) x ⟩
        0ℚ + x  <⟨ +-monoˡ-< x p ⟩
        x + x
    ∎)
    where open ℚ.≤-Reasoning

x-x≡0 : (x : ℚ) → (x - x ≡ 0ℚ)
x-x≡0 x = (begin
    x - x   ≡⟨ +-comm (x) (- x) ⟩
    - x + x ≡⟨ +-inverseˡ x ⟩
    0ℚ      ∎)
    where open ≡-Reasoning

p≡0⇒∣p∣≡0 : {p : ℚ} → p ≡ 0ℚ → ∣ p ∣ ≡ 0ℚ
p≡0⇒∣p∣≡0 eqz = trans (ℚ.0≤p⇒∣p∣≡p (≤-reflexive (sym eqz))) eqz

∣x-x∣<x : (x : ℚ) → 0ℚ < x → ∣ x - x ∣ < x
∣x-x∣<x x p = (begin-strict
    ∣ x - x ∣   ≡⟨ p≡0⇒∣p∣≡0 (x-x≡0 x) ⟩
    0ℚ          <⟨ p ⟩
    x           ∎)
    where open ℚ.≤-Reasoning

equilateral-triangle : (line : LineSegment) → .{ 0ℚ < LineSegment.lineLength line }
    → Σ (Triangle) (λ t → is-equilateral t)
equilateral-triangle line {p} = 
    let c1 = circle (LineSegment.from line) (LineSegment.lineLength line) (LineSegment.nonNegative line)
        c2 = circle (LineSegment.to line) (LineSegment.lineLength line) (LineSegment.nonNegative line)
        ((p0 , p1) , ((l0 , l1), _)) = circle-intersection c1 c2 line PointEq.refl PointEq.refl {x<x+x (LineSegment.lineLength line) p} {∣x-x∣<x (LineSegment.lineLength line) p}
    in
        (from-edges line l1 (line-sym l0) (refl , (refl , refl))) , (refl , refl)
   