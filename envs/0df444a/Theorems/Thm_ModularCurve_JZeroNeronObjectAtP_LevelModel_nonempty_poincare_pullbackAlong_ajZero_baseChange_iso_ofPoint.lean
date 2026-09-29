-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_ajZero_baseChange_iso_ofPoint
-- name    : ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_pullbackAlong_ajZero_baseChange_iso_ofPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/ca766f3b-bf82-50c0-b602-111d97b3a71a
-- title:
--   Base-changed Abel–Jacobi classifies 𝒪(y)⊗𝒪(-ε₀)
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$ with $p\nmid N_0$, a valuation subring $A$ of $\overline{\mathbf Q}$, and a level model $M$ of type `JZeroNeronObjectAtP.LevelModel N₀ p A`; write $\kappa$ for the residue field of $A$, made an algebra over the base ring `R p` through the ring homomorphism `M.toκ` recorded in $M$, and write $X_0 \to \operatorname{Spec}(R\,p)$ for the Igusa model `toBase0 N₀ p`. Assume its base change $X_{0,\kappa}\to\operatorname{Spec}\kappa$ is separated, and let `hD₀κ` be a datum representing, on the base-changed designation `M.D₀.baseChange κ`, the subfunctor of rigidified line bundles on $X_{0,\kappa}$ (rigidified along the base-changed cusp section `sectionBaseChange κ M.ε₀`) cut out by `algEquivZeroCut`, namely those whose restriction to every geometric fibre is algebraically equivalent to zero; assume further that the underlying module of the Poincaré bundle of `hD₀κ` is isomorphic to the transport `BaseChange.ofR` of the Poincaré bundle of `M.rep` pulled back along the first projection of $D_0\times_{R\,p}\kappa$. Then for every $\kappa$-point $y$ of $X_{0,\kappa}$, the pullback of the Poincaré bundle of `hD₀κ` along $y$ followed by the base change of $M$'s Abel–Jacobi morphism `M.aj₀` is isomorphic to the dual of the ideal sheaf module of the graph of $y$, tensored with the ideal sheaf module of the graph of the base-changed cusp section.
--
--   This is the special-fibre form of the defining property of the Abel–Jacobi morphism of the level-$N_0$ Jacobian model: it transports the pin $\mathrm{aj}_0(x)\mapsto \mathcal O(x)\otimes\mathcal O(-\varepsilon_0)$ at field-valued points across base change to the residue field $\kappa$ and across an arbitrary representability datum for the base-changed relative $\operatorname{Pic}^0$ functor. It is used in the identification of the Frobenius action on the special fibre of the Jacobian model with the pushforward of line bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_ajZero_baseChange_iso_ofPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel IsLocalRing
  ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_pullbackAlong_ajZero_baseChange_iso_ofPoint
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) :
    letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
    ∀ [IsSeparated (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀))
        (M.D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) M.ε₀ (ResidueField ↥A)
        (M.rep.poincare.pullbackAlong ⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))),
      Nonempty ((hD₀κ.poincare.pullbackAlong
          ⟨y.1 ≫ pullback.map (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)) M.D₀.toBase (specMap (R p) (ResidueField ↥A))
              M.aj₀.1 (𝟙 _) (𝟙 _) ((Category.comp_id _).trans M.aj₀.2.symm) ((Category.comp_id _).trans (Category.id_comp _).symm),
            (Category.assoc _ _ _).trans (((congrArg (y.1 ≫ ·) (pullback.lift_snd _ _ _)).trans
              ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝟙 _) y.2).trans (Category.comp_id _)))))⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) y.1 y.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))
            (𝟙 _ ≫ (sectionBaseChange (ResidueField ↥A) M.ε₀).1)
            ((Category.assoc _ _ _).trans ((congrArg (𝟙 _ ≫ ·) (sectionBaseChange (ResidueField ↥A) M.ε₀).2).trans
              (Category.comp_id _)))).idealModule) := by sorry
