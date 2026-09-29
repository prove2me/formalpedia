-- Prove2me | Theorems.Thm_ModularCurve_XOneP_modularUnit_dictionary_or_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.modularUnit_dictionary_or_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/bf2d0f40-feae-5f26-a5a3-7fc4fdf73779
-- title:
--   Dictionary for the modular unit on the two-chart model of X₁(Mp)
-- statement:
--   Let $p$ be a prime and $M \ge 5$ a nonzero natural number with $p \nmid M$; let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image under $\mathbb{Q} \to L$ of the function field $\mathrm{x1FunctionField}(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal and $\zeta$ is in the image of $A \to L$, with an $A$-algebra structure on $K$ compatible with $A \to L \to K$. Let $j \in K$ be nonzero with Laurent expansion the image of the $q$-expansion $\mathrm{jq}$, and let $X = \mathrm{TwoChartModel}\,A\,K\,j$, the pushout of the two charts, with structure morphism $\pi = \mathrm{modelTo}$ to $\operatorname{Spec} A$. Let $U \subseteq X$ be an open subscheme whose composite inclusion with $\pi$ is smooth of relative dimension $1$ and which contains every such open. Let $\varepsilon$ be a morphism $\operatorname{Spec} A \to X$ with $\varepsilon \circ \pi$ the identity (a section) whose image lies in $U$. Finally let $u, u'$ lie in the finite-chart subalgebra $\mathrm{chartAlgFin}\,A\,K\,j \subseteq K$, with $u$ mapping to the image of the modular unit series $\Delta(q)/\Delta(q^p)$, $u'$ to $p^{12}$ times the inverse of that series, and $u u' = p^{12}$ in the subalgebra. Then one of $u$, $u'$, say $v$, has the following property: for every algebraically closed field $k$ and every non-injective ring homomorphism $\varphi : A \to k$, for every point $\mathfrak{q}$ of $\mathrm{XFin}\,A\,K\,j = \operatorname{Spec}(\mathrm{chartAlgFin}\,A\,K\,j)$ with $v \notin \mathfrak{q}$, and every point $y$ of the pullback of $\pi$ along $\operatorname{Spec}\varphi$ whose first projection is the image of $\mathfrak{q}$ under the finite-chart morphism $\mathrm{ifFin}$-style inclusion $\mathrm{ιFin}$ into $X$, the point $y$ lies in the preimage of $U$ under the first projection, and moreover in the connected component of that preimage containing the image of the closed point of $k$ under the section of the geometric fibre induced by $\varepsilon$ and $\operatorname{Spec}\varphi$.
--
--   This is the "dictionary" step relating the modular units $\Delta(q)/\Delta(q^p)$ and its conjugate to the geometry of the characteristic-$p$ geometric fibres of the two-chart model of $X_1(Mp)$ over $A$: on each such fibre, the non-vanishing locus of one of the two units avoids the singular crossings and sits inside the single connected component of the smooth trace that contains the chosen section. It is used in the construction of a one-sided pool of points in the smooth locus ([`ModularCurve.XOneP.exists_oneSidedPool_smoothLocus_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_oneSidedPool_smoothLocus_twoChartModel_x1_mul)), and cites the degeneration analysis of this model, the non-smoothness of the special fibres, the comparison of images of the geometric special fibres, the irreducibility dichotomy for $u$ and $u'$, and the infinitude of closed points on a smooth integral curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_modularUnit_dictionary_or_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian TensorProduct

theorem ModularCurve.XOneP.modularUnit_dictionary_or_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j)) (hε : Set.range ε.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)))
    (u u' : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hu : ((u : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))
    (hu' : ((u' : ↥K) : LaurentSeries L) = (p : LaurentSeries L) ^ 12 * (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹)
    (huu' : u * u' = (p : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) ^ 12) :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k), ¬ Function.Injective φ →
        ∀ (𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j)), u ∉ 𝔮.asIdeal →
        ∀ y : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))),
          (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base y = (ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮 →
          y ∈ ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U :
              (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).Opens) : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ)))) ∧
          y ∈ connectedComponentIn
              ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U :
                (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).Opens) : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))))
              (((sectionFibrePoint ε (Spec.map (CommRingCat.ofHom φ))).1).base (IsLocalRing.closedPoint k))) ∨
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k), ¬ Function.Injective φ →
        ∀ (𝔮 : ↥(ModularCurve.TwoChart.XFin A (↥K) j)), u' ∉ 𝔮.asIdeal →
        ∀ y : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))),
          (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).base y = (ModularCurve.TwoChart.ιFin A (↥K) j).base 𝔮 →
          y ∈ ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U :
              (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).Opens) : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ)))) ∧
          y ∈ connectedComponentIn
              ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U :
                (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))).Opens) : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom φ))))
              (((sectionFibrePoint ε (Spec.map (CommRingCat.ofHom φ))).1).base (IsLocalRing.closedPoint k))) := by sorry
