-- Prove2me | Theorems.Thm_ModularCurve_XOneP_eq_of_comap_inclusion_eq_comap_inclusion_of_gaussPresentation_x1_mul_x1x0
-- name    : ModularCurve.XOneP.eq_of_comap_inclusion_eq_comap_inclusion_of_gaussPresentation_x1_mul_x1x0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/a0423e0b-72ca-5b17-a76a-1bd9df609d07
-- title:
--   Gauss valuation of X₁(Mp) is the unique extension from the floor
-- statement:
--   Fix a prime $p$ and $M \ge 5$ with $p \nmid M$ and $M \ne 0$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the $\mathbb{Q}$-rational $q$-expansion field [`ModularCurve.x1FunctionFieldC`](def/ModularCurve_X1.html#L134) of level $Mp$, i.e. the field generated over $\mathbb{Q}$ by the ratios of integral forms for $\Gamma_1(Mp)$, and let $K_1$ be the analogous field built from $\Gamma_1(M) \cap \Gamma_0(p)$, with $K_1 \le K$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, with $A$-algebra structures on $K$ and $K_1$ compatible with $L$, and let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ and $j_1 \in K_1$ be nonzero elements whose underlying Laurent series is the image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant. Let $W_0$ be a valuation subring of $K$ characterised by the Gauss presentation condition: $f \in W_0$ if and only if there are power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal and $f \cdot \hat{y} = \hat{x}$ in $\mathrm{LaurentSeries}\,L$, where $\hat{\phantom{x}}$ denotes the image under $A \to L$ followed by $\mathrm{PowerSeries} \to \mathrm{LaurentSeries}$. Then any valuation subring $W'$ of $K$ whose pullback along the inclusion $K_1 \hookrightarrow K$ coincides with the pullback of $W_0$ equals $W_0$.
--
--   This is the uniqueness half of the statement that the Gauss (multiplicative-branch) valuation of the function field of $X_1(Mp)$ over $A$ is the only valuation of that field lying above the Gauss valuation of the floor $X(\Gamma_1(M) \cap \Gamma_0(p))$, the ramification index being one and the residue extension — the Igusa field — having degree $p-1 = [K : K_1]$, so that the fundamental inequality $\sum_i e_i f_i \le [K:K_1]$ is already saturated by $W_0$. It is used in the construction and analysis of the two-chart integral model of $X_1(Mp)$, in particular to identify comaps of valuation subrings and to separate the Gauss valuation from its Galois conjugates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_eq_of_comap_inclusion_eq_comap_inclusion_of_gaussPresentation_x1_mul_x1x0.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XOneP.eq_of_comap_inclusion_eq_comap_inclusion_of_gaussPresentation_x1_mul_x1x0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))

    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₁ : ↥K₁) (hj₁ : ((j₁ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₁ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :

    ∀ W' : ValuationSubring ↥K,
      W'.comap (IntermediateField.inclusion hle).toRingHom = W₀.comap (IntermediateField.inclusion hle).toRingHom →
        W' = W₀ := by sorry
