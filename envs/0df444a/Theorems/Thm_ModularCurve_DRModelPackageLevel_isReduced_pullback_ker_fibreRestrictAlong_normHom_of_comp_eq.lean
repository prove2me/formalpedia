-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq
-- name    : ModularCurve.DRModelPackageLevel.isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7198860d-a8b1-5f0f-89ca-9a3b60ec0657
-- title:
--   Reducedness of the joint kernel of the two degeneracy maps mod p
-- statement:
--   Fix $N_0 \ge 1$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel` for these data, i.e. a Deligne–Rapoport style model package for the Igusa-type curves `X N₀ p` and `X0 N₀ p` over $\operatorname{Spec}$ of the coefficient ring `R p`, carrying in particular a cusp section $\mathfrak P.\varepsilon_{\inf}$ and two morphisms $\mathfrak P.\pi$, $\mathfrak P.\pi_w$ over the base. Both $\mathfrak P.\pi$ and $\mathfrak P.\pi_w$ are assumed finite, flat, locally of finite presentation, and of rank $p+1$ at every point. Let $D$ be a relative $\mathrm{Pic}^0$ designation (a scheme with structure morphism to the base and a zero section) for the structure morphism `toBase N₀ p`, together with `hD` exhibiting $D$ as representing the functor of rigidified line bundles along $\mathfrak P.\varepsilon_{\inf}$ satisfying the fibrewise algebraic-equivalence-to-zero condition `algEquivZeroCut`; similarly let $\varepsilon_0$ be a section of `toBase0 N₀ p`, and $D_0$, `hD₀` the corresponding designation and representability datum for `toBase0 N₀ p` and $\varepsilon_0$. Let $\delta_0,\delta_1 \colon D \to D_0$ be morphisms over the base such that, for every base scheme $t \colon T \to \operatorname{Spec}(\mathrm{R}\,p)$ and every $T$-point $a$ of $D$ over $t$, the pullback of the Poincaré bundle of $D_0$ along $a$ followed by $\delta_i$ is isomorphic to the rigidification along `rigSection` of the rank-$(p+1)$ norm module `normModule` (the $(p+1)$-st determinant of the pushforward, tensored with the dual of that of the structure sheaf) of the pullback of the Poincaré bundle of $D$ along $a$, taken along the base-changed $\mathfrak P.\pi$ for $i=0$ and along the base-changed $\mathfrak P.\pi_w$ for $i=1$. Assume further that the cusp section followed by $\mathfrak P.\pi$ equals $\varepsilon_0$, that $D$ is smooth over the base and $D_0$ smooth and proper over it. Then for every algebraically closed field $\kappa$ of characteristic $p$ and every morphism $c \colon \operatorname{Spec} \kappa \to \operatorname{Spec}(\mathrm{R}\,p)$, the scheme obtained as the fibre product over $D \times_{\mathrm{R}\,p} \kappa$ of the two fibres of the base-changed morphisms $(\delta_i)_\kappa$ over the unit section of the base-changed relative group law on $(D_0)_\kappa$ supplied by `hD₀` is reduced.
--
--   This is the reducedness of the special fibre of the joint kernel $\ker \delta_0 \cap \ker \delta_1$ of the two degeneracy (norm) morphisms on the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model, the geometric input behind the analysis of the $p$-fibre of $J_0(N_0p)$ used in Ribet's level-lowering argument. It is used by [`ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel`](thm.html#ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq.lean

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
import Definitions.Def_AlgebraicGeometry_NeronSpecialFibreRestriction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    [IsFinite 𝔓.π.1] [Flat 𝔓.π.1] [LocallyOfFinitePresentation 𝔓.π.1] (hrk : ∀ x, 𝔓.π.1.finrank x = p + 1)

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
    (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀)

    [IsFinite 𝔓.πw.1] [Flat 𝔓.πw.1] [LocallyOfFinitePresentation 𝔓.πw.1] (hrk_w : ∀ x, 𝔓.πw.1.finrank x = p + 1)

    (δ : Fin 2 → SchemeHomOver D.toBase D₀.toBase)
    (hδ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.π.1 𝔓.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδ₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.πw.1 𝔓.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))

    (hcusp : 𝔓.εinf.1 ≫ 𝔓.π.1 = ε₀.1)

    (hsm : Smooth D.toBase) (hsm₀ : Smooth D₀.toBase) (hpr₀ : IsProper D₀.toBase)

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (c : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of (R p))) :
    IsReduced
      (pullback
        (pullback.fst (NeronSpecialFibreInfra.fibreRestrictAlong c D₀.toBase D.toBase (δ 0)).1
          (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange c).one (𝟙 _)).1)
        (pullback.fst (NeronSpecialFibreInfra.fibreRestrictAlong c D₀.toBase D.toBase (δ 1)).1
          (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange c).one (𝟙 _)).1)) := by sorry
