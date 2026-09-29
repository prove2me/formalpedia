-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.Diamond.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/3f99be29-5e8f-53e3-ab56-dfb761a8b473
-- title:
--   Transcendence of j and finiteness of K over L(j)
-- statement:
--   Let $q$ be a prime, $M'\ge 1$ and $\ell_g$ a divisor of $M'$, and let $L$ be a field of characteristic $0$ that is algebraic over $\mathbb Q$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the unit-reduction map `ZMod.unitsMap (dvd_sq_mul q M')`, with the kernel of the unit-reduction map $(\mathbb Z/q^2M')^\times\to(\mathbb Z/\ell_g)^\times$ coming from $\ell_g\mid q^2M'$. Let $K\subseteq L(\!(\mathfrak q)\!)$ be the intermediate field generated over $L$ by the coefficientwise image under $\mathbb Q\to L$ of the rational $q$-expansion field `xHFunctionFieldC ℚ (q^2*M') H₁`, that is of `qExpFunctionFieldC ℚ (CohCarrier.GammaH (q^2*M') H₁)`. Let $A$ be a domain with an $A$-algebra structure on $L$ realising $L$ as the fraction field of $A$, together with a compatible $A$-algebra structure on $K$. Let $j\in K$ be an element whose underlying Laurent series is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the series $\mathfrak q^{-1}\cdot j_{\mathrm{num}}$. Then $j$ is transcendental over $A$, $K$ is finite-dimensional over $L(j)$, and $K/L(j)$ is separable.
--
--   These are the standing frame facts about the modular function field of level $H_1$: the $q$-expansion field of a finite-index subgroup containing the translation $T$ is a finite separable extension of the rational function field in $j$, and survives base change to $L$. They serve as the hypotheses of the integral two-chart model constructions for $K$, and are cited in the auxiliary-level-one and Diamond-operator chart statements at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.FullLevel.Diamond.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) :
    Transcendental A j ∧
    FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K ∧
    Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by sorry
