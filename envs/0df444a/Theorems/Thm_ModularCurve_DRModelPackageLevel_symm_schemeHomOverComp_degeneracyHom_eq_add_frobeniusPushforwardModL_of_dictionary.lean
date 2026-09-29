-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_symm_schemeHomOverComp_degeneracyHom_eq_add_frobeniusPushforwardModL_of_dictionary
-- name    : ModularCurve.DRModelPackageLevel.symm_schemeHomOverComp_degeneracyHom_eq_add_frobeniusPushforwardModL_of_dictionary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/dc4660bd-dc86-525f-b066-310bf498608b
-- title:
--   Ribet's matrix for the two degeneracy maps mod p
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$ with $p\nmid N_0$, and let $\mathfrak P$ be a Deligne–Rapoport level package `DRModelPackageLevel N₀ p hpN₀`, whose structure maps $\mathfrak P.\pi$ and $\mathfrak P.\pi_w$ from $X(N_0,p)$ to $X_0(N_0)$ over $R_p$ are assumed finite, flat and locally of finite presentation of rank $p+1$ at every point. Let $D$ (with $\mathfrak P.\varepsilon_{\inf}$) and $D_0$ (with a section $\varepsilon_0$) be relative $\mathrm{Pic}^0$ designations for `toBase N₀ p` and `toBase0 N₀ p`, together with data `hD`, `hD₀` exhibiting each as representing, by a Poincaré rigidified line bundle, the functor of rigidified line bundles that are fibrewise algebraically equivalent to zero. Let $\delta_0,\delta_1 : D\to D_0$ be $R_p$-morphisms such that, for every base $t$ and every point $a$ of $D$ over $t$, the pullback of the Poincaré bundle of $D_0$ along $a$ followed by $\delta_0$ (resp. $\delta_1$) is isomorphic to the $\varepsilon_0$-rigidification of the norm module $\det_{p+1}(\pi_*L)\otimes \det_{p+1}(\pi_*\mathcal O)^{\vee}$ formed along the base change of $\mathfrak P.\pi$ (resp. $\mathfrak P.\pi_w$) of $L=$ the pullback of the Poincaré bundle of $D$ along $a$. Let $\kappa$ be an algebraically closed field of characteristic $p$ over $R_p$, with representability data `hDκ`, `hD₀κ` for the $\kappa$-fibres whose Poincaré bundles are isomorphic to the base changes of those of $D$, $D_0$. Assume the first component map $\mathfrak P.\mathrm{comp}\,\kappa\,0$ of the special fibre carries $\varepsilon_0$ to $\varepsilon_{\inf}$, and let $\mathrm{abq}_0$ be the induced morphism $D_\kappa\to D_{0,\kappa}$ of representing objects, while $\mathrm{abq}_1$ is characterised by the analogous isomorphism with the norm module replaced by the plain pullback along the second component map. Let $\varphi_\kappa$ be the endomorphism of the $\kappa$-fibre of $X_0(N_0)$ given by the second component map followed by $\mathrm{fibreMap0}\,\mathfrak P.\pi$, assumed finite, flat, locally of finite presentation of rank $p$ at every point, and let $F$ be an endomorphism of $D_{0,\kappa}$ realising the rank-$p$ norm construction along $\varphi_\kappa$ in the same rigidified sense. Finally let $e$ be a bijection from $\mathrm{Pic}^0$ of the function field of $X_0(N_0)$ over $\kappa$ to the points of $D_0$ over $\mathrm{Spec}\,\kappa$, additive for the relative group law attached to `hD₀`, and intertwining the map induced by $F$ with `frobeniusPushforwardModL`. Then for every point $x$ of $D$ over $\mathrm{Spec}\,\kappa$, writing $\mathrm{Fr}_*$ for `frobeniusPushforwardModL κ N₀ p`, one has $e^{-1}(x\delta_0)=e^{-1}(\mathrm{abq}_0(x))+\mathrm{Fr}_*e^{-1}(\mathrm{abq}_1(x))$ and $e^{-1}(x\delta_1)=\mathrm{Fr}_*e^{-1}(\mathrm{abq}_0(x))+e^{-1}(\mathrm{abq}_1(x))$.
--
--   This is Ribet's matrix $\begin{pmatrix}1&\mathrm{Fr}_*\\ \mathrm{Fr}_*&1\end{pmatrix}$ for the pair of degeneracy maps $\pi_*,(w\pi)_*$ on the special fibre at $p$ of the Néron model of $J_0(N_0p)$, resting on the Deligne–Rapoport description of $X_0(N_0p)_{\mathbf F_p}$ as two copies of $X_0(N_0)_{\mathbf F_p}$ crossing at the supersingular points, on which $\pi$ acts as $(\mathrm{id},\mathrm{Frob})$ and $w\pi$ as $(\mathrm{Frob},\mathrm{id})$. It is used by [`ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel`](thm.html#ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel) to pin down the special-fibre data of the Néron model object at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_symm_schemeHomOverComp_degeneracyHom_eq_add_frobeniusPushforwardModL_of_dictionary.lean

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
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_FrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.symm_schemeHomOverComp_degeneracyHom_eq_add_frobeniusPushforwardModL_of_dictionary
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

    (hε₁' : (sectionBaseChange κ ε₀).1 ≫ 𝔓.comp κ (algebraMap (R p) κ) 0 = (sectionBaseChange κ 𝔓.εinf).1)

    (abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (habq₀ : abq 0 = RepresentsRelSubPic.pullbackHom (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp_over κ (algebraMap (R p) κ) 0)
      hε₁' hDκ hD₀κ)
    (habq₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) 1)
            (𝔓.comp_over κ (algebraMap (R p) κ) 1) t)).obj (hDκ.poincare.pullbackAlong a).L)))

    (φκ : fibre0 (N₀ := N₀) (algebraMap (R p) κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    (hφκ : φκ = 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ))
    (hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) κ = baseChange (R p) (toBase0 N₀ p) κ)
    [IsFinite φκ] [Flat φκ] [LocallyOfFinitePresentation φκ] (hφ_rk : ∀ x, φκ.finrank x = p)

    (F : SchemeHomOver (D₀.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (hF : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : SchemeHomOver t (D₀.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b F)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L)))

    (e : JZeroC κ N₀ ≃ SchemeHomOver (specMap (R p) κ) D₀.toBase)
    (he_add : ∀ u v : JZeroC κ N₀,
      e (u + v) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (e u) (e v))
    (he_frob : ∀ b : SchemeHomOver (specMap (R p) κ) D₀.toBase,
      e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap F b) = frobeniusPushforwardModL κ N₀ p (e.symm b)) :

    ∀ x : SchemeHomOver (specMap (R p) κ) D.toBase,
      e.symm (NeronModelInfra.schemeHomOverComp x (δ 0)) =
          e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap (abq 0) x) +
            frobeniusPushforwardModL κ N₀ p (e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap (abq 1) x)) ∧
      e.symm (NeronModelInfra.schemeHomOverComp x (δ 1)) =
          frobeniusPushforwardModL κ N₀ p (e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap (abq 0) x)) +
            e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap (abq 1) x) := by sorry
