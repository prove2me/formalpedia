-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_baseChange_normHom_eq_restrict_mul_frob_restrict_points
-- name    : ModularCurve.DRModelPackageLevel.baseChange_normHom_eq_restrict_mul_frob_restrict_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/1da527f7-d8d2-5d99-8bd1-20780ed02574
-- title:
--   Ribet's matrix on κ-points of Pic⁰
-- statement:
--   Fix a prime $p$ and $N_0$ with $p \nmid N_0$, and a Deligne–Rapoport model package $\mathfrak P$ of level $N_0$ at $p$; assume its forgetful map $\mathfrak P.\pi$ and its twisted map $\mathfrak P.\pi_w$ are finite, flat and locally of finite presentation, with constant fibre rank $p+1$. Let $D$ (resp. $D_0$) be a pointed scheme over $R\,p$ together with a datum $hD$ (resp. $hD_0$, for a section $\varepsilon_0$) representing the functor of rigidified line bundles on the curve `toBase N₀ p` rigidified at $\mathfrak P.\varepsilon_{\inf}$ (resp. on `toBase0 N₀ p` at $\varepsilon_0$) that are fibrewise algebraically equivalent to zero, with Poincaré bundle. Let $\delta_0,\delta_1 : D \to D_0$ be morphisms over $R\,p$ such that for every $t : T \to \operatorname{Spec}(R\,p)$ and every $T$-point $a$ of $D$, the Poincaré bundle of $hD_0$ pulled back along $a$ followed by $\delta_i$ is isomorphic to the rigidification, along the section `rigSection` and the projection, of the norm module in degree $p+1$ of the pullback of $hD$'s Poincaré bundle along $a$, taken for the base change to $T$ of $\mathfrak P.\pi$ (for $i=0$) resp. of $\mathfrak P.\pi_w$ (for $i=1$). Let $\kappa$ be an algebraically closed field of characteristic $p$ and an $R\,p$-algebra, with data $hD_\kappa$, $hD_{0\kappa}$ asserting that the base changes $D\times\kappa$, $D_0\times\kappa$ represent the corresponding functors for the base-changed curves and sections, and isomorphisms identifying their Poincaré bundles with the base changes of those of $hD$, $hD_0$. Let $\mathrm{abq}_0,\mathrm{abq}_1 : D\times\kappa \to D_0\times\kappa$ be morphisms over $\kappa$ such that the Poincaré bundle of $hD_{0\kappa}$ pulled back along $a$ followed by $\mathrm{abq}_i$ is isomorphic to the rigidification of the pullback of $hD_\kappa$'s Poincaré bundle along $a$ by the $T$-base change of $\mathfrak P.\mathrm{comp}\,\kappa\,i$, for all $T$-points $a$. Let $\varphi_\kappa$ be the endomorphism of the fibre `fibre0` at $\kappa$ given by $\mathfrak P.\mathrm{comp}\,\kappa\,1$ followed by `fibreMap0 𝔓.π`, compatible with the structure map, finite, flat, locally of finite presentation of constant fibre rank $p$, and let $F$ be an endomorphism of $D_0\times\kappa$ over $\kappa$ classifying, in the same sense, the rigidified norm module in degree $p$ along $\varphi_\kappa$. Then for every $\kappa$-point $a$ of $D\times\kappa$ (a point over the identity of $\operatorname{Spec}\kappa$), in the group law on $D_0\times\kappa$ supplied by $hD_{0\kappa}$ for the subgroup condition of fibrewise algebraic equivalence to zero: the $\kappa$-point obtained from $a$ by passing to $D$ over $\operatorname{Spec}(R\,p)$, composing with $\delta_0$ and descending again equals $(a \cdot \mathrm{abq}_0) + (a\cdot\mathrm{abq}_1\cdot F)$, and the same construction with $\delta_1$ equals $(a\cdot\mathrm{abq}_0\cdot F) + (a\cdot\mathrm{abq}_1)$, where juxtaposition denotes composition of a point with a morphism over the base.
--
--   This is Ribet's matrix for the two degeneracy maps $\pi_*$ and $(\pi w_p)_*$ read on the special fibre at $p$ of the Jacobian of the Deligne–Rapoport model of level $N_0p$, in the form of an identity of $\kappa$-points of the representing $\mathrm{Pic}^0$-schemes: restriction to the two components of the special fibre, composed with the Frobenius norm $F$, recovers the base change of each degeneracy map. It is the points-level form used by the downstream statements `fibreRestrictAlong_normHom_eq_lift_abq_comp_ribetMatrix`, `isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq` and `symm_schemeHomOverComp_degeneracyHom_eq_add_frobeniusPushforwardModL_of_dictionary`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_baseChange_normHom_eq_restrict_mul_frob_restrict_points.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.baseChange_normHom_eq_restrict_mul_frob_restrict_points
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

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)
      (algEquivZeroCut (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)) (D.baseChange κ))
    (hPκ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf κ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) κ), pullback.condition⟩)).L))
    (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)
      (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)) (D₀.baseChange κ))
    (hP₀κ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) ε₀ κ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) κ), pullback.condition⟩)).L))

    (abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (habq : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq i))).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) i) (𝔓.comp_over κ (algebraMap (R p) κ) i) t)).obj
            (hDκ.poincare.pullbackAlong a).L)))

    (φκ : fibre0 (N₀ := N₀) (algebraMap (R p) κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    (hφκ : φκ = 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ))
    (hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) κ = baseChange (R p) (toBase0 N₀ p) κ)
    [IsFinite φκ] [Flat φκ] [LocallyOfFinitePresentation φκ] (hφ_rk : ∀ x, φκ.finrank x = p)

    (F : SchemeHomOver (D₀.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (hF : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : SchemeHomOver t (D₀.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b F)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L))) :
    ∀ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (D.baseChange κ).toBase,
      RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 0)) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀κ).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp a (abq 0))
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a (abq 1)) F) ∧
      RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 1)) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀κ).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a (abq 0)) F)
          (NeronModelInfra.schemeHomOverComp a (abq 1)) := by sorry
