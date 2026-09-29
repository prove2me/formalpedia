-- Prove2me | Theorems.Thm_IntermediateField_finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver
-- name    : IntermediateField.finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/1785a066-347d-5fbb-938a-785c89fa16d1
-- title:
--   Form descent for one-variable function fields
-- statement:
--   Let $A_0$ be a discrete valuation domain, $L$ a field of characteristic zero and $\iota_0 : A_0 \to L$ an injective ring homomorphism. Let $K_0 \subseteq L$ be a subfield containing $\iota_0(A_0)$ and consisting of fractions of it (every $x \in K_0$ satisfies $x\,\iota_0(b) = \iota_0(a)$ for some $a, b \in A_0$ with $b \neq 0$), and assume every element of $L$ is algebraic over $K_0$. Let $F$ be an $L$-algebra which is a field, essentially of finite type over $L$, with `IsCurveOver L F`: every nonzero $f \in F$ admits a degree-zero divisor recording its orders at all places of $F/L$, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$. Assume every element of $F$ algebraic over $L$ lies in $L$. Let $F_0 \subseteq F$ be a subfield with $\mathrm{alg\,map}(c) \in F_0 \iff c \in K_0$ for $c \in L$, and such that every $f \in F$ can be written as a quotient $f \cdot \sum_i d_i g'_i = \sum_i c_i g_i$ with $c_i, d_i \in L$, $g_i, g'_i \in F_0$ and $\sum_i d_i g'_i \neq 0$ (both sums of the same length). Let $j_0 : A_0 \to F_0$ be a ring homomorphism compatible with $\iota_0$ under $L \to F$. Then, for the resulting algebra structures $A_0 \to F_0$, $A_0 \to K_0$ and $K_0 \to F_0$: $K_0$ is a fraction field of $A_0$; $A_0, K_0, F_0$ form a scalar tower; some $t \in F_0$ is transcendental over $A_0$; for every such $t$, $F_0$ is finite-dimensional and separable over $K_0(t)$; and $A_0$ is integrally closed in $F_0$.
--
--   This is the descent step asserting that a $K_0$-form $F_0$ of a one-variable function field $F/L$ — cut out by the conditions $F_0 \cap L = K_0$ and $F = L \cdot F_0$ — is itself a one-variable function field over $K_0$, with $A_0$ integrally closed in it. It supplies the field-theoretic input to [`AlgebraicGeometry.exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian`](thm.html#AlgebraicGeometry.exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian), where the conclusions are exactly the hypotheses needed to build a normal proper model over $A_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem IntermediateField.finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    {L : Type} [Field L] [CharZero L] (ι₀ : A₀ →+* L) (hι₀ : Function.Injective ι₀)
    (K₀ : Subfield L) (hK₀A : ∀ a : A₀, ι₀ a ∈ K₀)
    (hK₀ : ∀ x : L, x ∈ K₀ → ∃ a b : A₀, b ≠ 0 ∧ x * ι₀ b = ι₀ a)

    (hLK₀ : ∀ x : L, IsAlgebraic ↥K₀ x)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (hLalg : ∀ x : F, IsAlgebraic L x → x ∈ Set.range (algebraMap L F))
    (F₀ : Subfield F)
    (hconst : ∀ c : L, algebraMap L F c ∈ F₀ ↔ c ∈ K₀)
    (hspan : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (g : Fin n → ↥F₀) (d : Fin n → L) (g' : Fin n → ↥F₀),
      (∑ i, d i • (g' i : F)) ≠ 0 ∧ f * (∑ i, d i • (g' i : F)) = ∑ i, c i • (g i : F))

    (j₀ : A₀ →+* ↥F₀) (hj₀ : ∀ a : A₀, ((j₀ a : ↥F₀) : F) = algebraMap L F (ι₀ a))
    :
    letI : Algebra A₀ ↥F₀ := j₀.toAlgebra
    letI : Algebra A₀ ↥K₀ := (ι₀.codRestrict K₀ hK₀A).toAlgebra
    letI : Algebra ↥K₀ ↥F₀ :=
      (((algebraMap L F).comp K₀.subtype).codRestrict F₀ (fun c => (hconst (c : L)).mpr c.2)).toAlgebra
    IsFractionRing A₀ ↥K₀ ∧ IsScalarTower A₀ ↥K₀ ↥F₀ ∧
    (∃ t : ↥F₀, Transcendental A₀ t) ∧
    (∀ t : ↥F₀, Transcendental A₀ t →
      FiniteDimensional ↥(IntermediateField.adjoin ↥K₀ ({t} : Set ↥F₀)) ↥F₀ ∧
      Algebra.IsSeparable ↥(IntermediateField.adjoin ↥K₀ ({t} : Set ↥F₀)) ↥F₀) ∧
    IsIntegrallyClosedIn A₀ ↥F₀ := by sorry
