-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_smoothLocus_maximal_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_smoothLocus_maximal_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/bc3a77a6-bc06-5a39-a764-313e50d584c7
-- title:
--   Maximal smooth locus of the two-chart model of X₁(Mp)
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((q))$ which equals [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((q))$ generated over $L$ by the image, under the coefficientwise map $L((q)) \leftarrow \mathbb{Q}((q))$ induced by $\mathbb{Q} \to L$, of the $q$-expansion function field of $\Gamma_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with an algebra structure over which $L$ is its fraction field, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A \to L$, together with a compatible $A$-algebra structure on $K$. Let $j \in K$ be nonzero with image in $L((q))$ the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant, transported to $L$ coefficientwise. Write $X$ for [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229), the pushout of the two Spec-maps from the spectrum of the middle chart algebra to the spectra of the subalgebras $A[j]$ and $A[j^{-1}]$ of $K$, and $c : X \to \operatorname{Spec} A$ for the morphism [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) obtained from the two structure maps of those subalgebras. The conclusion is that there exists an open subscheme $U \subseteq X$ such that the composite of the inclusion $U \hookrightarrow X$ with $c$ is smooth of relative dimension $1$, and such that every open $W \subseteq X$ with the same property satisfies $W \le U$; that is, $c$ has a largest open locus of smoothness of relative dimension one. The proof uses none of the hypotheses $5 \le M$, $p \nmid M$, the descriptions of $\zeta$, $K$, $j$, or the conditions on $p$ and $\zeta$ in $A$: it applies to an arbitrary morphism of schemes.
--
--   This provides the maximal smooth locus of the two-chart integral model of $X_1(Mp)$ over the discrete valuation ring $A$, the open subscheme over which one works when comparing Picard groups of the model with those of its fibres. It is cited by the statements about sections, reductions and Picard-group projections for this model in the good-reduction analysis of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_smoothLocus_maximal_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem ModularCurve.XOneP.exists_smoothLocus_maximal_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    :
    ∃ U : (ModularCurve.TwoChartModel A (↥K) j).Opens,
      SmoothOfRelativeDimension 1 (U.ι ≫ ModularCurve.TwoChart.modelTo A (↥K) j) ∧
      ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens,
        SmoothOfRelativeDimension 1 (W.ι ≫ ModularCurve.TwoChart.modelTo A (↥K) j) → W ≤ U := by sorry
