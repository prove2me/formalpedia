-- Prove2me | Theorems.Thm_ModularCurve_XOne_forall_exists_mul_residue_eq_and_mem_iff_exists_mul_eq_gaussValuationSubring_chartAlgFin_x1
-- name    : ModularCurve.XOne.forall_exists_mul_residue_eq_and_mem_iff_exists_mul_eq_gaussValuationSubring_chartAlgFin_x1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/9c577585-8ad4-550a-b1b4-3796174999b5
-- title:
--   Gauss valuation ring as a localisation of the chart ring
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K_1$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the coefficientwise image under $\mathbb{Q} \to L$ of the $q$-expansion function field of $\Gamma_1(M)$. Let $A$ be a discrete valuation domain with fraction field $L$, such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, equipped with an $A$-algebra structure on $K_1$ compatible with the tower $A \to L \to K_1$, and let $\varpi$ generate the maximal ideal of $A$. Let $j \in K_1$ be nonzero with image in $\mathrm{LaurentSeries}\,L$ the coefficientwise image of $q^{-1}$ times the $j$-numerator power series, i.e. the $q$-expansion of the $j$-invariant. Let $W_0$ be a valuation subring of $K_1$ consisting exactly of those $f$ for which there are power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$ and $f \cdot y = x$ in $\mathrm{LaurentSeries}\,L$ after mapping coefficients to $L$ (the Gauss valuation ring), and assume every element of the subalgebra $S = \mathrm{chartAlgFin}\,A\,K_1\,j$ of elements of $K_1$ integral over $A[j]$ lies in $W_0$. The conclusion is twofold: first, every element $e$ of the residue field of $W_0$ satisfies $e \cdot \rho(t) = \rho(s)$ for some $s, t \in S$ with $t$ not in the nonunits of $W_0$, where $\rho$ denotes reduction to the residue field of $W_0$; second, for every $f \in K_1$, one has $f \in W_0$ if and only if $f \cdot s = c$ for some $c, s \in S$ with $s$ not in the nonunits of $W_0$.
--
--   This identifies the Gauss valuation ring $W_0$ of the base-changed $q$-expansion field of $X_1(M)$ with the localisation of the finite chart ring $S$ (the integral closure of $A[j]$ in $K_1$) at the prime $S \cap \mathfrak{m}_{W_0}$, and its residue field with the fraction field of the image of $S$. It feeds the statement that this localisation is a discrete valuation ring with the expected fraction field, used in the construction of the integral model of $X_1(M)$ near the Gauss point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOne_forall_exists_mul_residue_eq_and_mem_iff_exists_mul_eq_gaussValuationSubring_chartAlgFin_x1.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XOne.forall_exists_mul_residue_eq_and_mem_iff_exists_mul_eq_gaussValuationSubring_chartAlgFin_x1
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K₁)
    (hW₀ : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hSW₀ : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀) :
    (∀ e : IsLocalRing.ResidueField ↥W₀, ∃ s t : ↥(chartAlgFin A (↥K₁) j), (t : ↥K₁) ∉ W₀.nonunits ∧
      e * IsLocalRing.residue ↥W₀ ⟨(t : ↥K₁), hSW₀ t⟩ = IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩) ∧
    (∀ f : ↥K₁, f ∈ W₀ ↔ ∃ c s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∉ W₀.nonunits ∧ f * (s : ↥K₁) = (c : ↥K₁)) := by sorry
