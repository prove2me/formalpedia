-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
-- name    : ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/06f2a444-9db0-5ebf-a97c-05638f73653d
-- title:
--   Poincaré bundle at a degree-zero class as a point twist
-- statement:
--   Fix $N_0$ and a prime $p$ with $p \nmid N_0$, a Deligne–Rapoport level package $\mathfrak P$ for $(N_0,p)$ whose structure morphism `toBase N₀ p` $: X \to \operatorname{Spec} R_p$ is proper, and a relative $\mathrm{Pic}^0$ designation $D$ over $R_p$ (a scheme $D.P$ with a morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} R_p$ and a zero section). Assume $h_D$: $D$ represents, relative to the section $\mathfrak P.\varepsilon_{\inf}$, the subfunctor of rigidified line bundles that are fibrewise algebraically trivial at all algebraically closed geometric points, with universal object $h_D.\mathrm{poincare}$; assume the analogous datum $h_{D_{\mathbb Q}}$ over $\mathbb Q$ for the base change of the curve, together with an isomorphism $h_{PQ}$ between its Poincaré bundle and the base change along $R_p \to \mathbb Q$ of the restriction of $h_D.\mathrm{poincare}$ to the generic fibre. Assume further: a morphism $\mathrm{aj}_{\mathbb Q}$ from $X_{\mathbb Q}$ to $(D.\mathrm{baseChange}\ \mathbb Q).\mathrm{toBase}$ over $\operatorname{Spec}\mathbb Q$ carrying the base-changed section $\varepsilon_{\inf}$ to the zero section, and satisfying the Abel–Jacobi normalisation: for every field $K$, every $t \colon \operatorname{Spec} K \to \operatorname{Spec}\mathbb Q$ and every $K$-point $x$ of $X_{\mathbb Q}$ over $t$, the pullback of $h_{D_{\mathbb Q}}.\mathrm{poincare}$ along $x$ followed by $\mathrm{aj}_{\mathbb Q}$ is isomorphic to the dual of the ideal sheaf of the graph of $x$ tensored with the ideal sheaf module of the graph of $t$ followed by $\varepsilon_{\inf}$; a morphism $k_{\mathbb Q}$ from $X \times_{R_p} \overline{\mathbb Q}$ to $X \times_{R_p} \mathbb Q$ compatible with both projections (the second up to $\operatorname{Spec} \mathbb{Q} \leftarrow \operatorname{Spec}\overline{\mathbb Q}$); the composite $\overline{\mathrm{aj}} = \mathfrak P.\mathrm{eeta} \circ$-then-$k_{\mathbb Q}$-then-$\mathrm{aj}_{\mathbb Q}$-then-first projection, from the geometric model $\mathfrak P.\mathrm{Meta}.C$ to $D.P$, lying over `genPt p`; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak P.\mathrm{Meta}.C$ whose image in $X$ is $\varepsilon_{\inf}$ and with $\bar\varepsilon \circ \overline{\mathrm{aj}}$ the zero section; and a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0$ of the geometric modular function field of level $N_0p$ onto the $\overline{\mathbb Q}$-points of $D$ over `genPt p`, additive for the relative group law induced by $h_D$ through the group-theoretic version of the algebraic-triviality cut, and such that for all $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak P.\mathrm{Meta}.C$ with $s$ lying over $\varepsilon_{\inf}$ there is a degree-zero divisor with divisor $[\,\mathrm{place}(x)\,]-[\,\mathrm{place}(s)\,]$ whose class is sent by $\mathrm{pts}$ to $x \circ \overline{\mathrm{aj}}$. Given $n$, points $q_i$ ($i \in \mathrm{Fin}\ n$) of $\mathfrak P.\mathrm{Meta}.C$ over $\overline{\mathbb Q}$, points $x_i$ of $X$ over `genPt p` with $x_i$ the image of $q_i$, natural numbers $\mathrm{pos}_i, \mathrm{neg}_i$ with $\sum_i(\mathrm{pos}_i-\mathrm{neg}_i)=0$, and a degree-zero divisor $D_x$ equal to $\sum_i (\mathrm{pos}_i-\mathrm{neg}_i)\,[\mathrm{place}(q_i)]$, the conclusion is that the pullback of $h_D.\mathrm{poincare}$ along $\mathrm{pts}([D_x])$ has underlying module isomorphic to the iterated tensor product, folded from the right over $i = 0,\dots,n-1$ starting from the unit module on $X \times_{R_p} \overline{\mathbb Q}$, of the dual of the $\mathrm{pos}_i$-th power of the graph ideal of $x_i$ tensored with the $\mathrm{neg}_i$-th power of that graph ideal.
--
--   This is the Abel–Jacobi normalisation of the Poincaré bundle on the Deligne–Rapoport model: it computes the line bundle classified by the point $\mathrm{pts}([D_x])$ of the relative $\mathrm{Pic}^0$ scheme as the corresponding twist by the sections $x_i$, for an arbitrary degree-zero combination of $\overline{\mathbb Q}$-points of the geometric modular curve. It feeds the identification of $\mathrm{pts}$ on divisor classes with a morphism determined by twists of sections, used in the construction of the Néron-type object attached to $J_0(N_0p)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist.lean

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

theorem ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
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
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    {n : ℕ} (q : Fin n → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (x : Fin n → SchemeHomOver (genPt p) (toBase N₀ p))
    (hxq : ∀ i, (x i).1 = (q i).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))

    (pos neg : Fin n → ℕ) (hn : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0)
    (Dx : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))))
    (hDx : (Dx : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
      ∑ i, Finsupp.single (𝔓.Meta.pointEquivPlace (q i)) ((pos i : ℤ) - (neg i : ℤ))) :
    Nonempty ((hD.poincare.pullbackAlong (pts (Pic0.mk Dx))).L ≅
      ((List.finRange n).foldr
          (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I ^ (pos i)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I ^ (neg i)).module ⊗ M)
          (𝟙_ (pullback (toBase N₀ p) (genPt p)).Modules))) := by sorry
