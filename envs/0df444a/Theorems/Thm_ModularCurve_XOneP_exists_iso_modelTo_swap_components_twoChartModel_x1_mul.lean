-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_iso_modelTo_swap_components_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_iso_modelTo_swap_components_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/e8aa8260-a8fc-5ada-8b8c-5bbe3d63b55f
-- title:
--   A level-p involution swapping bad-fibre components of X₁(Mp)
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero that is a cyclotomic extension of type $\{p\}$ of $\mathbb{Q}$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image under the coefficient map [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with $A$-algebra structures on $L$ and on $K$, compatible as a scalar tower, such that $L$ is the fraction field of $A$, the image of $p$ lies in the maximal ideal of $A$, and $\zeta$ lies in the image of $A$; let $j \in K$ be an element whose image in $\mathrm{LaurentSeries}\,L$ is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), with $j \ne 0$. Write $X =$ [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) (the pushout of the two chart inclusions) and $\pi =$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) for its structure morphism to $\operatorname{Spec} A$. Let $U \subseteq X$ be an open subscheme such that the composite $U \hookrightarrow X \to \operatorname{Spec} A$ is smooth of relative dimension $1$, and maximal with this property (every open $W$ with the same property satisfies $W \le U$). Let $\varepsilon$ be a section of $\pi$, i.e. a morphism $\operatorname{Spec} A \to X$ whose composite with $\pi$ is the identity, whose set-theoretic image lies in $U$. Then there exist an automorphism $\sigma$ of $X$ with $\sigma \circ \pi$-compatibility $\sigma_{\mathrm{hom}}$ followed by $\pi$ equal to $\pi$, a section $\varepsilon'$ of $\pi$ with $\varepsilon'$ equal to $\varepsilon$ followed by $\sigma_{\mathrm{hom}}$, such that $\sigma_{\mathrm{hom}}^{-1}(U) = U$ and the image of $\varepsilon'$ lies in $U$, with the following property: for every $f \in A$, every algebraically closed field $k$ and every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} A_f$ from the localisation away from $f$, if the fibre $X_{A_f} \times_{\operatorname{Spec} A_f} \operatorname{Spec} k \to \operatorname{Spec} k$ is not smooth, then, writing $U_s$ for the preimage of $U$ in that fibre under the two projections and $C$ for the connected component of the point $\varepsilon(s)$ (the base change of $\varepsilon$ to $A_f$ evaluated at $s$, taken at the closed point of $\operatorname{Spec} k$) inside $U_s$, both: every $y$ in $C$ has its image under the base change of $\sigma_{\mathrm{hom}}$ to this fibre in $U_s \setminus C$; and the point $\varepsilon'(s)$ lies in $U_s \setminus C$.
--
--   This is the level-$p$ (Atkin–Lehner type) involution of the regular two-chart model of $X_1(Mp)$ over a discrete valuation ring containing $\zeta_p$ and residue characteristic $p$: it is an automorphism over the base, hence preserves the maximal relatively smooth open $U$, and on each non-smooth geometric fibre it carries the component of the smooth locus through a given section to the other component (classically, it interchanges the Igusa and the étale component). It supplies the second, "far-side" section used in [`ModularCurve.XOneP.exists_twoSidedPool_smoothLocus_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_twoSidedPool_smoothLocus_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_iso_modelTo_swap_components_twoChartModel_x1_mul.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian TensorProduct

theorem ModularCurve.XOneP.exists_iso_modelTo_swap_components_twoChartModel_x1_mul
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
    :
    ∃ (σ : ModularCurve.TwoChartModel A (↥K) j ≅ ModularCurve.TwoChartModel A (↥K) j)
      (hσ : σ.hom ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j)
      (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j)) (_ : ε.1 ≫ σ.hom = ε'.1)
      (_ : σ.hom ⁻¹ᵁ U = U)
      (_ : Set.range ε'.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j))),
      ∀ f : A,
      ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))),
        ¬ Smooth (pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s) →
        (∀ y : ↥(pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s),
          y ∈ connectedComponentIn
              (((pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))) ⁻¹ᵁ U :
                  (pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s))
              (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k)) →
          (pullback.map (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s
              (curveChange σ.hom hσ (specMap A (Localization.Away f))) (𝟙 _) (𝟙 _)
              ((Category.comp_id _).trans (curveChange_snd _ _ _).symm)
              ((Category.comp_id _).trans (Category.id_comp _).symm)).base y ∈
            (((pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))) ⁻¹ᵁ U :
                  (pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s)) \
            connectedComponentIn
              (((pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))) ⁻¹ᵁ U :
                  (pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s))
              (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))) ∧
        ((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε') s).1).base (IsLocalRing.closedPoint k) ∈
            (((pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))) ⁻¹ᵁ U :
                  (pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s)) \
            connectedComponentIn
              (((pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (Localization.Away f))) ⁻¹ᵁ U :
                  (pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (Localization.Away f)) s))
              (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k)) := by sorry
