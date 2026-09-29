-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_isPrime_mem_of_forall_coeff_mem_maximalIdeal_chartAlgFin_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.Diamond.exists_isPrime_mem_of_forall_coeff_mem_maximalIdeal_chartAlgFin_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/56e606dd-0b21-582c-8ae2-eff74b45df61
-- title:
--   Gauss prime on the j-chart of X_{H_1}(q²M')
-- statement:
--   Fix a prime $q$, an integer $M'\ge 1$, a divisor $\ell_g \mid M'$, and a field $L$ of characteristic $0$ together with a valuation subring $A_0 \subseteq L$ that is assumed to be a discrete valuation ring with $q \in \mathfrak m_{A_0}$. Let $H_1 \le (\mathbb Z/q^2M')^\times$ be the subgroup consisting of the units congruent to $1$ modulo $q$ (the kernel of reduction defining [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22)) intersected with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$, and let $K \subseteq L(\!(\mathfrak q)\!)$ be the intermediate field obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$, with $A_0$ acting on $K$ compatibly with $L$. Let $j \in K$ be nonzero with Laurent expansion the coefficientwise image of the $q$-expansion $\mathfrak q^{-1}\!\cdot$`jNumQ` of the modular invariant. Then the subalgebra $C$ of elements of $K$ integral over $A_0[j]$ carries a prime ideal $G$ such that: there is a valuation subring $W_0 \subseteq K$ characterised by $f \in W_0$ iff $f\,y = x$ in $L(\!(\mathfrak q)\!)$ for some $x,y \in A_0[\![\mathfrak q]\!]$ with $\bar y \ne 0$, and $h \in G$ iff $h$ is a nonunit of $W_0$; every $h \in C$ all of whose Laurent coefficients come from $\mathfrak m_{A_0}$ lies in $G$; the image of $q$ lies in $G$; and if $f \in A_0[X]$ satisfies $f(j) \in G$ then all coefficients of $f$ lie in $\mathfrak m_{A_0}$.
--
--   This is the construction of the Gauss prime attached to the cusp (Igusa component) on the $j$-finite chart of the integral model of $X_{H_1}(q^2M')$, in the level-$H_1$ edition: the contraction to the chart algebra of the maximal ideal of the Gauss valuation ring of the $q$-expansion field, recorded together with the properties needed downstream (residual vanishing of $q$, residual transcendence of $j$). It feeds the construction of a place of the chart algebra whose residue data matches the origin chart of the level automorphism in the Diamond-type argument at auxiliary level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_isPrime_mem_of_forall_coeff_mem_maximalIdeal_chartAlgFin_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.Diamond.exists_isPrime_mem_of_forall_coeff_mem_maximalIdeal_chartAlgFin_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L] (A₀ : ValuationSubring L)
    (hdvr : IsDiscreteValuationRing ↥A₀)
    (hq𝔪 : ((q : ↥A₀)) ∈ IsLocalRing.maximalIdeal ↥A₀)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥A₀ ↥K] [IsScalarTower ↥A₀ L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ G : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j), G.IsPrime ∧
      (∃ W₀ : ValuationSubring ↥K,
        (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) ∧
        ∀ h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j), h ∈ G ↔
          ((h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j)) : ↥K) ∈ W₀.nonunits) ∧
      (∀ h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j),
        (∀ n : ℤ, ∃ a : ↥A₀, a ∈ IsLocalRing.maximalIdeal ↥A₀ ∧
          (a : L) = (((h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j)) : ↥K) : LaurentSeries L).coeff n) →
        h ∈ G) ∧
      algebraMap ↥A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j) (q : ↥A₀) ∈ G ∧
      (∀ f : Polynomial ↥A₀,
        Polynomial.aeval (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₀ (↥K) j) f ∈ G →
          ∀ i : ℕ, f.coeff i ∈ IsLocalRing.maximalIdeal ↥A₀) := by sorry
