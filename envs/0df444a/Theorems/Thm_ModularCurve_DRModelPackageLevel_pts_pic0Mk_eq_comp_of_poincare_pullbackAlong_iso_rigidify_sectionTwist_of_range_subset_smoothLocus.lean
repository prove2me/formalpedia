-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_range_subset_smoothLocus
-- name    : ModularCurve.DRModelPackageLevel.pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_range_subset_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/920287aa-fde7-56d8-96b8-2493c3335f26
-- title:
--   Geometric generic restriction of a smooth-locus A-point of Pic⁰
-- statement:
--   Fix $N_0$ with $N_0\neq 0$ and a prime $p$ with $p\nmid N_0$, and a Deligne–Rapoport model package $\mathfrak P$ of level $N_0p$ over $R=R_p$, whose structure morphism `toBase N₀ p` $:X\to\operatorname{Spec}R$ is proper. Let $D$ consist of a scheme $P$ over $\operatorname{Spec}R$ together with a zero section, and let `hD` represent the relative sub-Picard functor of $(X,\varepsilon_{\inf})$ cut out by fibrewise algebraic equivalence to zero: a rigidified Poincaré bundle on $X\times_R P$ satisfying the condition, with the universal property that every such rigidified bundle on $X\times_R T$ is the pullback of it along a unique $T$-point of $P$. Assume the analogous representability `hDQ` after base change to $\mathbb Q$, together with `hPQ` identifying the rational Poincaré bundle with the base change of the pullback of `hD.poincare` along `pullback.fst`; a generic-fibre Abel–Jacobi morphism `ajQ` sending the $\varepsilon$-section to the zero section and satisfying, for every field $K$, every $K$-point $t$ of $\operatorname{Spec}\mathbb Q$ and every $x$ over $t$ of the rational curve, that the pullback of the rational Poincaré bundle along $x$ followed by `ajQ` is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of $t$ followed by the $\varepsilon$-section; a comparison morphism `kQ` from $X\times_R\overline{\mathbb Q}$ to $X\times_R\mathbb Q$ compatible with both projections (`hkQ₁`, `hkQ₂`); a morphism `ajbar` on $\mathfrak P.\mathrm{Meta}.C$ given as `eeta` followed by `kQ`, `ajQ` and `pullback.fst`, lying over the geometric generic point, and a $\overline{\mathbb Q}$-section `εbar` of $\mathfrak P.\mathrm{Meta}.C$ lying over $\varepsilon_{\inf}$ and sent by `ajbar` to the zero section. Assume further a bijection `pts` from $\mathrm{Pic}^0$ of the geometric modular function field of level $N_0p$ onto the $\overline{\mathbb Q}$-points of $P$, which is additive for the relative group law obtained from `hD` (`hpts_add`), Galois-equivariant (`hpts_galois`), and pinned on Abel–Jacobi classes: for all $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak P.\mathrm{Meta}.C$ with $s$ lying over $\varepsilon_{\inf}$ there is a degree-zero divisor equal to $[x]-[s]$ under `pointEquivPlace` whose class is sent by `pts` to $x$ followed by `ajbar`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ and $\rho:R\to A$ a ring homomorphism inducing the structural map $R\to\overline{\mathbb Q}$. Let $s_1,\dots,s_n$ be $A$-valued sections of $X$ whose images lie in $\mathfrak P.\mathrm{smoothLocus}$, let $q_1,\dots,q_n$ be $\overline{\mathbb Q}$-sections of $\mathfrak P.\mathrm{Meta}.C$ restricting to the $s_i$ over $\overline{\mathbb Q}$, let $\mathrm{pos},\mathrm{neg}:\{1,\dots,n\}\to\mathbb N$ satisfy $\sum_i(\mathrm{pos}_i-\mathrm{neg}_i)=0$, and let $D_x$ be the degree-zero divisor $\sum_i(\mathrm{pos}_i-\mathrm{neg}_i)[q_i]$. Finally let $a$ be an $A$-point of $P$ such that the pullback of `hD.poincare` along $a$ is isomorphic to the rigidification, along the $\varepsilon_{\inf}$-section of $X\times_R A$ and the projection to $\operatorname{Spec}A$, of the iterated tensor product over $i$ of the dual of the $\mathrm{pos}_i$-th power of the ideal of the divisor of $s_i$ with the $\mathrm{neg}_i$-th power of that ideal. Then `pts` applied to the class of $D_x$ equals the restriction of $a$ along $\operatorname{Spec}$ of the inclusion $A\hookrightarrow\overline{\mathbb Q}$.
--
--   This is the compatibility between the divisor-class dictionary on $J_0(N_0p)(\overline{\mathbb Q})$ and integral points of the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model: a class supported at points that spread out to $A$-valued sections in the smooth locus is the geometric generic restriction of the corresponding $A$-point. It is used downstream in the statements that points of $J_0$ extend over places of $\overline{\mathbb Q}$ above $p$ and in the comparison of the toric part at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_range_subset_smoothLocus.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.DRModelPackageLevel.pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_range_subset_smoothLocus
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
    (hsm : ∀ i, Set.range (s i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)))
    (q : Fin n → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hqs : ∀ i, (q i).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) =
      Spec.map (CommRingCat.ofHom A.subtype) ≫ (s i).1)

    (pos neg : Fin n → ℕ) (hn : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0)
    (Dx : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))))
    (hDx : (Dx : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
      ∑ i, Finsupp.single (𝔓.Meta.pointEquivPlace (q i)) ((pos i : ℤ) - (neg i : ℤ)))

    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (ha : Nonempty ((hD.poincare.pullbackAlong a).L ≅
        Scheme.Modules.rigidify (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf)
          (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)))
          ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules)))) :
    (pts (Pic0.mk Dx)).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ a.1 := by sorry
