-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_fibre_w_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange
-- name    : ModularCurve.XHDRModelAtP.fibre_w_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/314289a6-fa2c-5ec0-a7e4-1f41f9041239
-- title:
--   At non-smooth fibres, w moves the ε_∞-component off itself
-- statement:
--   Fix a prime $p$ and a non-zero natural number $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field over $\mathbb{Q}$ of the full group $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, i.e. a bundle of data for the integral model `X p (ΓM M H) hj` with its structure morphism `toBase p (ΓM M H) hj` to $\operatorname{Spec}$ of the base ring `R p`; among its fields are an open `𝔛.smoothLocus` of the model, sections `𝔛.εinf` and `𝔛.εzero` over the base, and a morphism `𝔛.w` over the base (with compatibility `𝔛.w_over`). Let $f$ be an element of `R p`, let $k$ be an algebraically closed field and let $s \colon \operatorname{Spec} k \to \operatorname{Spec}(\mathrm{Localization.Away}\ f)$ be a point, and assume the geometric fibre at $s$ is not smooth: the second projection of the pullback of the base change of `toBase p (ΓM M H) hj` to $\mathrm{Localization.Away}\ f$ along $s$ is not `Smooth`. Write $X_s$ for that pullback, $U_s \subseteq X_s$ for the preimage of `𝔛.smoothLocus` under the first projection of $X_s$ followed by the first projection of the base change, and $C_\infty$ for the connected component of $U_s$ containing the image of the closed point of $\operatorname{Spec} k$ under the fibre point attached to the base change of `𝔛.εinf` to $\mathrm{Localization.Away}\ f$. Then, first, every point $y$ of $X_s$ lying in $C_\infty$ is carried by the map on underlying spaces induced by `𝔛.w` (transported to $X_s$ via `curveChange` along `specMap (R p) (Localization.Away f)` and then by the pullback map with identities in the other two slots) into $U_s \setminus C_\infty$; and second, the image of the closed point of $\operatorname{Spec} k$ under the fibre point attached to the base change of `𝔛.εzero` also lies in $U_s \setminus C_\infty$.
--
--   At a geometric fibre of the $\Gamma_H$-model in characteristic $p$ (where, since $p \parallel M$, the Deligne–Rapoport fibre is a union of two components meeting at the supersingular points), this records that the involution $w$ interchanges the component of the smooth locus through the cusp $\infty$ with another component, and that the cusp $0$ lies on the latter. It supplies the separation hypothesis for the three existence results producing a two-sided pool of points in the smooth locus above a closed prime (for $p \ge 5$, $p = 3$ and $p = 2$).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_fibre_w_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange.lean

import Mathlib
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
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.fibre_w_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) (f : R p)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (hns : ¬ Smooth (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s)) :
        (∀ y : ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s),
          y ∈ connectedComponentIn
              (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                  (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
              (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) →
          (pullback.map (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s
              (curveChange 𝔛.w.hom 𝔛.w_over (specMap (R p) (Localization.Away f))) (𝟙 _) (𝟙 _)
              ((Category.comp_id _).trans (curveChange_snd _ _ _).symm)
              ((Category.comp_id _).trans (Category.id_comp _).symm)).base y ∈
            (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                  (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s)) \
            connectedComponentIn
              (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                  (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
              (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) ∧
        ((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εzero) s).1).base (IsLocalRing.closedPoint k) ∈
            (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                  (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s)) \
            connectedComponentIn
              (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                  (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
              (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) := by sorry
