-- Prove2me | Theorems.Thm_ModularCurve_XOneP_isReduced_pullback_toBase_twoChartIntegralModel_x1_mul
-- name    : ModularCurve.XOneP.isReduced_pullback_toBase_twoChartIntegralModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/d1da4733-db3a-541e-b751-ebc0d84177d9
-- title:
--   Reducedness of the mod p fibre of the two-chart model of X₁(Mp)
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the image, under the coefficientwise map $\mathrm{LaurentSeries}\,\mathbb{Q} \to \mathrm{LaurentSeries}\,L$ induced by $\mathbb{Q} \to L$, of the $q$-expansion function field [`ModularCurve.qExpFunctionFieldC ℚ (Gamma1 (M * p))`](def/ModularCurve_X1.html#L101). Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A \to L$, and let $K$ carry an $A$-algebra structure compatible with $A \to L \to K$. Let $j \in K$ be nonzero with image in $\mathrm{LaurentSeries}\,L$ the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the Laurent series $q^{-1}$ times the rational $j$-numerator power series. Finally let $k$ be a field of characteristic $p$ with an $A$-algebra structure. Then the pullback of the structure morphism [`AlgebraicCurve.TwoChartIntegralModel.toBase A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258) from the two-chart integral model — the pushout of the two affine morphisms `fFin` and `fInf`, which glues $\mathrm{Spec}$ of the subalgebras `chartAlg A K {j}` and `chartAlg A K {j⁻¹}` of $K$ along their common middle chart — to $\mathrm{Spec}\,A$ along $\mathrm{Spec}$ of $A \to k$ is a reduced scheme.
--
--   This is the multiplicity-one statement for the special fibre of the two-chart integral model of $X(\Gamma_1(M) \cap \Gamma_1(p))$ over a discrete valuation ring containing $\zeta_p$: both Igusa components occur with multiplicity one, so the fibre over any characteristic $p$ field is reduced (adjoining $\zeta_p$ is essential here). It feeds the subsequent analysis of the special fibre of this model — its irreducible components, the associated curve models and the Abel–Jacobi comparison used in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_isReduced_pullback_toBase_twoChartIntegralModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneP.isReduced_pullback_toBase_twoChartIntegralModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [CharP k p] [Algebra A k] :
    IsReduced (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A k)))) := by sorry
