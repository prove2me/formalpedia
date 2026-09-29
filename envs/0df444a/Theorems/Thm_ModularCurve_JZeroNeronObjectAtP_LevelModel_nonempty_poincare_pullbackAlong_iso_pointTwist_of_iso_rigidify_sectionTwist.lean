-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
-- name    : ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/61a24918-e2e3-5e03-8d30-ad69d149fcce
-- title:
--   Rigidified section twists restrict to the geometric generic fibre
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $p$ prime, a valuation subring $A$ of $\overline{\mathbf Q}$, and a level model $M : \mathtt{LevelModel } N_0\, p\, A$; write $f =$ `toBase0 N₀ p` for the Igusa scheme morphism $X_0(N_0) \to \operatorname{Spec} \mathbf Z_{(p)}$ of the model, assumed proper and smooth of relative dimension $1$, and let $\operatorname{Spec}(M.\rho) : \operatorname{Spec} A \to \operatorname{Spec}\mathbf Z_{(p)}$ be induced by the structure homomorphism $M.\rho$. Let $n$ be a natural number, $\sigma : \mathrm{Fin}\, n \to$ sections of $f$ over $\operatorname{Spec}(M.\rho)$ (morphisms $\operatorname{Spec} A \to X_0(N_0)$ composing with $f$ to $\operatorname{Spec}(M.\rho)$), let $\mathrm{pos},\mathrm{neg} : \mathrm{Fin}\, n \to \mathbf N$, and let $b$ be a point of $M.D_0.\mathrm{toBase}$ over $\operatorname{Spec}(M.\rho)$. Assume there is an isomorphism between the pullback along $b$ of the Poincaré rigidified line bundle $M.\mathrm{rep}.\mathrm{poincare}$ and the `rigidify` of the iterated tensor product $\bigotimes_i (I_{\sigma_i}^{\mathrm{pos}_i})^{\vee} \otimes I_{\sigma_i}^{\mathrm{neg}_i}$, folded over `List.finRange n` starting from the tensor unit of the modules on $X_0(N_0) \times_{\mathbf Z_{(p)}} \operatorname{Spec} A$, where $I_{\sigma_i}$ is the ideal sheaf of the graph of $\sigma_i$ (the relative effective Cartier divisor `RelEffCartierDiv.ofPoint`), and `rigidify` means tensoring with the pullback along $\mathrm{pullback.snd}$ of the dual of the restriction along the rigidifying section attached to $M.\varepsilon_0$. Let further $x : \mathrm{Fin}\, n \to$ points of $f$ over `genPt p` and $b_\eta$ a point of $M.D_0.\mathrm{toBase}$ over `genPt p`, obtained from $\sigma$ and $b$ by composing with `barPt A` $: \operatorname{Spec}\overline{\mathbf Q} \to \operatorname{Spec} A$. The conclusion is that the pullback along $b_\eta$ of the Poincaré bundle is isomorphic to the corresponding fold $\bigotimes_i (I_{x_i}^{\mathrm{pos}_i})^{\vee} \otimes I_{x_i}^{\mathrm{neg}_i}$ over the tensor unit on $X_0(N_0) \times_{\mathbf Z_{(p)}} \operatorname{Spec}\overline{\mathbf Q}$, with no rigidifying twist.
--
--   This is the base-change compatibility which transports a description of a Poincaré-bundle pullback as a twist by sections, valid over the valuation ring $A$, to the geometric generic fibre, where the rigidification is trivial because the base is the spectrum of a field. It is used in the identification of specialisations of degree-zero divisor classes on $X_0(N_0)$, in [`ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization`](thm.html#ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist.lean

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

theorem ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : JZeroNeronObjectAtP.LevelModel N₀ p A)

    [IsProper (toBase0 N₀ p)] [SmoothOfRelativeDimension 1 (toBase0 N₀ p)]

    {n : ℕ} (σ : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase0 N₀ p)) (pos neg : Fin n → ℕ)
    (b : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) M.D₀.toBase)
    (hb : Nonempty ((M.rep.poincare.pullbackAlong b).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ)) M.ε₀)
          (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ)))
          ((List.finRange n).foldr
            (fun i N => ((RelEffCartierDiv.ofPoint (toBase0 N₀ p) (σ i).1 (σ i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase0 N₀ p) (σ i).1 (σ i).2).I ^ (neg i)).module ⊗ N)
            (𝟙_ (pullback (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ))).Modules))))

    (x : Fin n → SchemeHomOver (genPt p) (toBase0 N₀ p)) (hx : ∀ i, (x i).1 = barPt A ≫ (σ i).1)
    (bη : SchemeHomOver (genPt p) M.D₀.toBase) (hbη : bη.1 = barPt A ≫ b.1) :
    Nonempty ((M.rep.poincare.pullbackAlong bη).L ≅
      ((List.finRange n).foldr
          (fun i N => ((RelEffCartierDiv.ofPoint (toBase0 N₀ p) (x i).1 (x i).2).I ^ (pos i)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (toBase0 N₀ p) (x i).1 (x i).2).I ^ (neg i)).module ⊗ N)
          (𝟙_ (pullback (toBase0 N₀ p) (genPt p)).Modules))) := by sorry
