-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_smoothOfRelativeDimension_one_toBase_twoChartIntegralModel_laurentBaseChange_gamma0_of_not_dvd
-- name    : ModularCurve.FullLevel.smoothOfRelativeDimension_one_toBase_twoChartIntegralModel_laurentBaseChange_gamma0_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/a0588105-577a-57f0-a415-5cd0ab2ff111
-- title:
--   Two-chart model of X₀(M') is smooth of relative dimension one
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$, and let $L$ be a field of characteristic zero. Let $K_0$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ which equals [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))`](def/ModularCurve_LaurentCoeff.html#L103), that is: the subfield of $L((q))$ generated over $L$ by the coefficientwise images under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) (the map induced by $\mathbb{Q} \to L$ on Laurent coefficients) of the elements of the intermediate field of $\mathbb{Q} \subseteq \mathrm{LaurentSeries}\,\mathbb{Q}$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f/\mathrm{intSeriesC}\,\mathbb{Q}\,p_g$ of integral $q$-expansions of modular forms $f, g$ of equal weight for $\Gamma_0(M')$ with nonzero denominator. Let $A$ be a discrete valuation ring (a domain) with a fraction field structure $A \subseteq L$, such that the image of $q$ in $A$ lies in the maximal ideal of $A$, together with an $A$-algebra structure on $K_0$ compatible with $A \to L \to K_0$. Let $j_0 \in K_0$ be nonzero and have $q$-expansion the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the Laurent series $q^{-1}$ times the rational power series `jNumQ`. Then the structure morphism [`AlgebraicCurve.TwoChartIntegralModel.toBase A K₀ j₀`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258) to $\operatorname{Spec} A$ — the morphism out of the pushout of $\operatorname{Spec}$ of the two chart algebras `chartAlg A K₀ {j₀}` and `chartAlg A K₀ {j₀⁻¹}` along their common localisation, descended from their $A$-algebra structure maps — is smooth of relative dimension $1$.
--
--   This is the good-reduction statement for $X_0(M')$ at a prime $q$ not dividing the level, in the form: the two-chart integral model of the ($L$-base-changed) $q$-expansion function field of $\Gamma_0(M')$ over an arbitrary discrete valuation ring $A$ with $q$ in its maximal ideal is smooth of relative dimension one over $\operatorname{Spec} A$. It feeds the construction of Igusa-style base models, in particular the Dedekind-domain and regular-fibre statements for the chart algebras at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_smoothOfRelativeDimension_one_toBase_twoChartIntegralModel_laurentBaseChange_gamma0_of_not_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.smoothOfRelativeDimension_one_toBase_twoChartIntegralModel_laurentBaseChange_gamma0_of_not_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)] :
    SmoothOfRelativeDimension 1 (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₀) j₀) := by sorry
