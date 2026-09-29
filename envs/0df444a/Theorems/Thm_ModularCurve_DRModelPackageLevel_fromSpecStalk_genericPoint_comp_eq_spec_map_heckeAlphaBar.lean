-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_fromSpecStalk_genericPoint_comp_eq_spec_map_heckeAlphaBar
-- name    : ModularCurve.DRModelPackageLevel.fromSpecStalk_genericPoint_comp_eq_spec_map_heckeAlphaBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/d803702b-caf2-51a3-8b95-a22debb92a4b
-- title:
--   Degeneracy morphism on generic points is Spec of α
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, let $\mathfrak{P}$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀` for level $N_0p$ over $\mathbf{Z}_{(p)}$, let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ and let $M$ be a level datum `LevelModel N₀ p A`. The package carries a curve model $\mathfrak{P}.\mathrm{Meta}$ over $\overline{\mathbf{Q}}$ whose function field is identified by `ffEquiv` with `modularFunctionFieldBar (N₀ * p)`, together with an isomorphism $\mathfrak{P}.\mathrm{eeta}$ onto the base change of `toBase N₀ p` along the geometric generic point; $M$ carries similarly a curve model $M.\mathrm{Meta}_0$ over $\overline{\mathbf{Q}}$ with function field `modularFunctionFieldBar N₀` and an isomorphism $M.\mathrm{eeta}_0$ onto the base change of `IgusaScheme.igusaTo N₀ p` along `genPt p`. Let $\pi_M : \mathfrak{P}.\mathrm{Meta}.C \to M.\mathrm{Meta}_0.C$ be a morphism of schemes such that (i) $\pi_M$ followed by $M.\mathrm{eeta}_0$ and the first projection of the pullback agrees with $\mathfrak{P}.\mathrm{eeta}$ followed by the first projection and then by the underlying morphism $\mathfrak{P}.\pi.1$ of the package's degeneracy datum, which goes from the level-$N_0p$ scheme to the level-$N_0$ Igusa scheme, and (ii) $\pi_M$ followed by $M.\mathrm{Meta}_0.\mathrm{toBase}$ equals $\mathfrak{P}.\mathrm{Meta}.\mathrm{toBase}$, so that $\pi_M$ is a $\overline{\mathbf{Q}}$-morphism. Then the canonical morphism from the spectrum of the stalk at the generic point of $\mathfrak{P}.\mathrm{Meta}.C$, followed by $\pi_M$, equals $\operatorname{Spec}$ of the ring homomorphism obtained by transporting `heckeAlphaBar (AlgebraicClosure ℚ) N₀ p`, the inclusion `modularFunctionFieldBar N₀ ⊆ modularFunctionFieldBar (N₀ * p)` of Laurent base changes induced by the degeneracy $N_0 \mid N_0p$, through $M.\mathrm{Meta}_0.\mathrm{ffEquiv}^{-1}$ on the source and $\mathfrak{P}.\mathrm{Meta}.\mathrm{ffEquiv}$ on the target, followed by the corresponding morphism from the spectrum of the stalk at the generic point of $M.\mathrm{Meta}_0.C$.
--
--   This says that the forgetful degeneracy morphism $X_0(N_0p) \to X_0(N_0)$, transported to the smooth proper $\overline{\mathbf{Q}}$-models of the two modular function fields, induces on generic points exactly $\operatorname{Spec}$ of the first degeneracy embedding $\alpha : \overline{\mathbf{Q}}(X_0(N_0)) \hookrightarrow \overline{\mathbf{Q}}(X_0(N_0p))$ of $q$-expansion fields. It is the step from which [`ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi`](thm.html#ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi) deduces that $\pi$ sends a rational point of the geometric generic fibre to the place lying under it along $\alpha$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_fromSpecStalk_genericPoint_comp_eq_spec_map_heckeAlphaBar.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel
  ModularCurve.JZeroNeronObjectAtP AlgebraicCurve

theorem ModularCurve.DRModelPackageLevel.fromSpecStalk_genericPoint_comp_eq_spec_map_heckeAlphaBar
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A)

    (πM : 𝔓.Meta.C ⟶ M.Meta₀.C)
    (hπM₁ : πM ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.π.1)
    (hπM₂ : πM ≫ M.Meta₀.toBase = 𝔓.Meta.toBase) :
    𝔓.Meta.C.fromSpecStalk (genericPoint 𝔓.Meta.C) ≫ πM =
      Spec.map (CommRingCat.ofHom
        (𝔓.Meta.ffEquiv.toRingHom.comp ((heckeAlphaBar (AlgebraicClosure ℚ) N₀ p).toRingHom.comp
          M.Meta₀.ffEquiv.symm.toRingHom))) ≫
        M.Meta₀.C.fromSpecStalk (genericPoint M.Meta₀.C) := by sorry
