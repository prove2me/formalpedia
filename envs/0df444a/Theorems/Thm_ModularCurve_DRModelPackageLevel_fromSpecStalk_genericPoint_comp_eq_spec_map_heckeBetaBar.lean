-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_fromSpecStalk_genericPoint_comp_eq_spec_map_heckeBetaBar
-- name    : ModularCurve.DRModelPackageLevel.fromSpecStalk_genericPoint_comp_eq_spec_map_heckeBetaBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/9e4d56e1-a856-5733-818e-1acdce538069
-- title:
--   Second degeneracy map on generic points is Specβ
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$ with $p\nmid N_0$, and let $\mathfrak P$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀`; among its data are the scheme `X N₀ p` proper, flat and integral over `Spec (R p)` via `toBase N₀ p`, a curve model $\mathfrak P.\mathrm{Meta}$ over $\overline{\mathbf Q}$ (an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\overline{\mathbf Q}$) together with an isomorphism `ffEquiv` of `modularFunctionFieldBar (N₀ * p)` with its function field, an isomorphism `𝔓.eeta` of $\mathfrak P.\mathrm{Meta}.C$ with the fibre of `toBase N₀ p` over the $\overline{\mathbf Q}$-point of the base, and a morphism `𝔓.πw` whose underlying scheme morphism `𝔓.πw.1` goes from `X N₀ p` to the Igusa scheme `IgusaScheme N₀ p`. Let $A$ be a valuation subring of $\overline{\mathbf Q}$ and $M$ a `LevelModel N₀ p A`, which provides in particular a curve model $M.\mathrm{Meta}_0$ over $\overline{\mathbf Q}$ with function field identified with `modularFunctionFieldBar N₀` by its own `ffEquiv`, and an isomorphism `M.eeta₀` of $M.\mathrm{Meta}_0.C$ with the fibre of `IgusaScheme.igusaTo N₀ p` over the $\overline{\mathbf Q}$-point `genPt p`. Assume given a morphism $\pi_M:\mathfrak P.\mathrm{Meta}.C\to M.\mathrm{Meta}_0.C$ such that (i) $\pi_M$ followed by `M.eeta₀` and the projection of the fibre to `IgusaScheme N₀ p` agrees with `𝔓.eeta` followed by the projection to `X N₀ p` and then by `𝔓.πw.1`, and (ii) $\pi_M$ followed by $M.\mathrm{Meta}_0.\mathrm{toBase}$ is $\mathfrak P.\mathrm{Meta}.\mathrm{toBase}$, so that $\pi_M$ is a morphism over $\overline{\mathbf Q}$. The conclusion is that the canonical morphism $\operatorname{Spec}$ of the stalk at the generic point of $\mathfrak P.\mathrm{Meta}.C$ into $\mathfrak P.\mathrm{Meta}.C$, followed by $\pi_M$, coincides with $\operatorname{Spec}$ of the ring homomorphism $M.\mathrm{Meta}_0.C.\mathrm{functionField}\to\mathfrak P.\mathrm{Meta}.C.\mathrm{functionField}$ obtained by composing the inverse of $M.\mathrm{Meta}_0.\mathrm{ffEquiv}$, the $\overline{\mathbf Q}$-algebra map `heckeBetaBar (AlgebraicClosure ℚ) N₀ p` from `laurentBaseChange` of the level-$N_0$ modular function field to that of level $N_0p$ (the second degeneracy embedding, given by `heckeBetaBarRingHom`), and $\mathfrak P.\mathrm{Meta}.\mathrm{ffEquiv}$, followed by the analogous morphism $\operatorname{Spec}$ of the stalk at the generic point of $M.\mathrm{Meta}_0.C$ into $M.\mathrm{Meta}_0.C$.
--
--   This identifies, at the level of generic points and function fields, the transported second degeneracy morphism $w$ followed by $\pi$ between the smooth $\overline{\mathbf Q}$-models of $X_0(N_0p)$ and $X_0(N_0)$ with $\operatorname{Spec}$ of the Atkin–Lehner-twisted degeneracy embedding $\beta$ on $q$-expansions. It is used by [`ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw`](thm.html#ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw), which converts it into the corresponding statement about closed points and places of the two function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_fromSpecStalk_genericPoint_comp_eq_spec_map_heckeBetaBar.lean

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

theorem ModularCurve.DRModelPackageLevel.fromSpecStalk_genericPoint_comp_eq_spec_map_heckeBetaBar
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A)

    (πM : 𝔓.Meta.C ⟶ M.Meta₀.C)
    (hπM₁ : πM ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.πw.1)
    (hπM₂ : πM ≫ M.Meta₀.toBase = 𝔓.Meta.toBase) :
    𝔓.Meta.C.fromSpecStalk (genericPoint 𝔓.Meta.C) ≫ πM =
      Spec.map (CommRingCat.ofHom
        (𝔓.Meta.ffEquiv.toRingHom.comp ((heckeBetaBar (AlgebraicClosure ℚ) N₀ p).toRingHom.comp
          M.Meta₀.ffEquiv.symm.toRingHom))) ≫
        M.Meta₀.C.fromSpecStalk (genericPoint M.Meta₀.C) := by sorry
