-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
-- name    : ModularCurve.JZeroNeronObjectAtP.LevelModel.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/ef2bbc22-2ade-51a1-8ce6-e101776add51
-- title:
--   Degree-zero twists by A-sections come from D₀
-- statement:
--   Fix a nonzero $N_0$ and a prime $p$, a valuation subring $A$ of $\overline{\mathbf Q}$, and a level model $M$ of type `LevelModel N₀ p A`, so that in particular $M$ provides a ring map $\rho$ from the base ring at $p$ to $A$, a unit section $\varepsilon_0$ of $c :=$ `toBase0 N₀ p` $: X_0(N_0) \to \operatorname{Spec}(R_p)$, a designation $M.D_0$ of the relative $\mathrm{Pic}^0$ with its Poincaré rigidified line bundle $M.\mathrm{rep}.\mathrm{poincare}$. Assume $c$ is proper, smooth of relative dimension $1$ and geometrically integral. Let $t := \operatorname{Spec}(\rho) : \operatorname{Spec} A \to \operatorname{Spec}(R_p)$, let $\sigma_0,\dots,\sigma_{n-1}$ be morphisms $\operatorname{Spec} A \to X_0(N_0)$ with $\sigma_i$ followed by $c$ equal to $t$, and let $\mathrm{pos}_i,\mathrm{neg}_i$ be natural numbers with $\sum_i (\mathrm{pos}_i - \mathrm{neg}_i) = 0$ in $\mathbf Z$. The assertion is that there exists a morphism $b : \operatorname{Spec} A \to M.D_0.\mathrm{toBase}$ over $t$ such that the underlying module of the pullback of the Poincaré bundle along $b$ is isomorphic to the following module on $P := X_0(N_0) \times_{\operatorname{Spec}(R_p)} \operatorname{Spec} A$: take $T$ to be the iterated tensor product, over $i$ in `List.finRange n`, of the dual of the module of $I_i^{\mathrm{pos}_i}$ with the module of $I_i^{\mathrm{neg}_i}$, starting from the tensor unit, where $I_i$ is the ideal sheaf on $P$ of the degree-one relative effective Cartier divisor cut out by the point $\sigma_i$ (the kernel ideal of its graph), and the module of an ideal sheaf is the kernel of the unit map to the pushforward along the associated closed immersion; then re-rigidify, forming $T \otimes q^{*}\big((s^{*}T)^{\vee}\big)$, where $q$ is the second projection $P \to \operatorname{Spec} A$ and $s : \operatorname{Spec} A \to P$ is the section determined by $\varepsilon_0$ and $t$.
--
--   This is the Abel–Jacobi statement in the smooth case: a degree-zero combination of $A$-valued sections of the smooth proper model of $X_0(N_0)$ at $p$ is represented by an $A$-point of the relative $\mathrm{Pic}^0$ designated by $M.D_0$, the corresponding rigidified line bundle being the canonical rigidification of the section twist. It is used in comparing specialised $J_0$-points with Picard-group pairs, in [`ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization`](thm.html#ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.JZeroNeronObjectAtP.LevelModel.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : JZeroNeronObjectAtP.LevelModel N₀ p A)

    [IsProper (toBase0 N₀ p)] [SmoothOfRelativeDimension 1 (toBase0 N₀ p)] [GeometricallyIntegral (toBase0 N₀ p)]
    {n : ℕ} (σ : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase0 N₀ p)) (pos neg : Fin n → ℕ)
    (hdeg : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0) :
    ∃ b : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) M.D₀.toBase,
      Nonempty ((M.rep.poincare.pullbackAlong b).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ)) M.ε₀)
          (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ)))
          ((List.finRange n).foldr
            (fun i N => ((RelEffCartierDiv.ofPoint (toBase0 N₀ p) (σ i).1 (σ i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase0 N₀ p) (σ i).1 (σ i).2).I ^ (neg i)).module ⊗ N)
            (𝟙_ (pullback (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ))).Modules))) := by sorry
