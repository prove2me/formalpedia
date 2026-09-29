-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_pts_pic0Mk_eq_barPt_comp_of_poincare_pullbackAlong_iso_ofPoint_tensor_idealModule
-- name    : ModularCurve.XHDRModelAtP.pts_pic0Mk_eq_barPt_comp_of_poincare_pullbackAlong_iso_ofPoint_tensor_idealModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/b5662149-9621-55b6-a9c2-0dc177cb9da3
-- title:
--   A-point with Poincaré bundle 𝒪(u₁-u₂) computes pts([y₁]-[y₂])
-- statement:
--   Fix a prime $p$, a nonzero level $M$ with $p \mid M$, a subgroup $H \le (\mathbb Z/M)^\times$, and the hypothesis $hj$ that $jqModC\ \mathbb Q$ lies in the $q$-expansion function field of full level; let $\mathfrak X$ be a model datum `XHDRModelAtP p M H hpM hj` over $R\,p$, with `toBase p (ΓM M H) hj` proper. Let $D$ be a relative $\mathrm{Pic}^0$ designation over $R\,p$ for this curve (a scheme $D.P$ with structure morphism $D.toBase$ and a zero section), and let $hD$, respectively $hDQ$, assert that $D$, respectively its base change to $\mathbb Q$, represents the functor of line bundles rigidified along the section $\mathfrak X.\varepsilon_{\infty}$ and fibrewise algebraically equivalent to zero, with Poincaré bundles $hD.poincare$, $hDQ.poincare$; $hPQ$ compares the latter with the base change to $\mathbb Q$ of the former. Further data: an Abel–Jacobi morphism $ajQ$ over $\mathbb Q$ carrying the section to the zero section and satisfying, for every field $K$, every $t : \mathrm{Spec}\,K \to \mathrm{Spec}\,\mathbb Q$ and every $t$-point $x$ of the curve, $(x \circ ajQ)^*hDQ.poincare \cong \mathcal O(x) \otimes \mathcal I(t \circ \varepsilon)$; a comparison morphism $kQ$ between the geometric generic and the $\mathbb Q$-base-change fibres; the induced morphism $ajbar$ from the curve model $\mathfrak X.\mathrm{Meta}$ over $\overline{\mathbb Q}$ to $D.P$ over `genPt p`; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ compatible with $\mathfrak X.\varepsilon_\infty$ and sent by $ajbar$ to the zero section; and a bijection $pts$ from $J_H = \mathrm{Pic}^0(\overline{\mathbb Q}, xHFunctionFieldBar\ M\ H)$ onto the $\overline{\mathbb Q}$-points of $D.toBase$ which is additive for the relative group law attached to $hD$, Galois-equivariant, and pinned so that for all $\overline{\mathbb Q}$-points $x$ and $s$ with $s$ compatible with $\varepsilon_\infty$ the class of $[\mathrm{place}(x)] - [\mathrm{place}(s)]$ goes to $x \circ ajbar$. Now let $A$ be a valuation subring of $\overline{\mathbb Q}$ and $\rho : R\,p \to A$ a ring homomorphism whose composite with the inclusion is the structure map to $\overline{\mathbb Q}$; let $y_1, y_2$ be $\overline{\mathbb Q}$-points of $\mathfrak X.\mathrm{Meta}.C$ and $u_1, u_2$ sections of the curve over $\mathrm{Spec}\,\rho$ whose restrictions along $A \hookrightarrow \overline{\mathbb Q}$ are $y_1, y_2$ and whose images lie in $\mathfrak X.smoothLocus$; let $Dv$ be the degree-zero divisor $[\mathrm{place}(y_1)] - [\mathrm{place}(y_2)]$; and let $a$ be a point of $D.P$ over $\mathrm{Spec}\,\rho$ with $a^*hD.poincare \cong \mathcal O(u_1) \otimes \mathcal I(u_2)$, the tensor product of the line bundle of the relative effective Cartier divisor of $u_1$ with the ideal module of that of $u_2$. Then the $\overline{\mathbb Q}$-point $pts$ of the class of $Dv$ equals $a$ restricted along $A \hookrightarrow \overline{\mathbb Q}$.
--
--   This is the integral-to-generic comparison for the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model of $X_H(M)$ at $p \mid M$: an $A$-valued point of the representing scheme whose Poincaré pullback is $\mathcal O(u_1 - u_2)$ for two $A$-sections in the smooth locus is recognised, on the geometric generic fibre, as the point attached to the divisor class $[y_1] - [y_2]$. It is used in the proofs that points of $J_H$ of the form $[x] - [s]$ extend to the valuation ring $A$, i.e. in the statements [`ModularCurve.XHDRModelAtP.extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter`](thm.html#ModularCurve.XHDRModelAtP.extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter) and [`ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_single_sub_single_of_mem_range_comp`](thm.html#ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_single_sub_single_of_mem_range_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_pts_pic0Mk_eq_barPt_comp_of_poincare_pullbackAlong_iso_ofPoint_tensor_idealModule.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.pts_pic0Mk_eq_barPt_comp_of_poincare_pullbackAlong_iso_ofPoint_tensor_idealModule
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)
    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JH M H,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu₁ : Spec.map (CommRingCat.ofHom A.subtype) ≫ u₁.1 =
      y₁.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    (hu₁sm : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu₂ : Spec.map (CommRingCat.ofHom A.subtype) ≫ u₂.1 =
      y₂.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    (hu₂sm : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))

    (Dv : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hDv : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)

    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (ha : Nonempty ((hD.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule)) :
    (pts (Pic0.mk Dv)).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ a.1 := by sorry
