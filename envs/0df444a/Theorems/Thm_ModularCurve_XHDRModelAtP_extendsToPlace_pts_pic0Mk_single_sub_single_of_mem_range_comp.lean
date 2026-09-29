-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_extendsToPlace_pts_pic0Mk_single_sub_single_of_mem_range_comp
-- name    : ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_single_sub_single_of_mem_range_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/11ddfd13-a3f0-5f99-8642-f874f4819f09
-- title:
--   Pairs of places on one component extend to A-points
-- statement:
--   Fix a prime $p$, an integer $M\neq 0$ with $p\mid M$ and $p^{2}\nmid M$, a subgroup $H\le(\mathbb Z/M)^{\times}$, and the hypothesis $hj$ that $j$, as a $q$-expansion over $\mathbb Q$, lies in the function field of level $SL(2,\mathbb Z)$; let $\mathfrak X$ be an integral model `XHDRModelAtP p M H hpM hj` at $p$ of the curve of level $\Gamma_H(M)$, with its associated curve model $\mathfrak X.\mathrm{Meta}$ over $\overline{\mathbb Q}$ with function field `xHFunctionFieldBar M H`, its identification `𝔛.eeta` of $\mathfrak X.\mathrm{Meta}.C$ with the geometric generic fibre, and its section `𝔛.εinf`. Assume the structure morphism `toBase` is proper. The Picard data consist of: a designation $D$ (a scheme $D.P$ over $\operatorname{Spec}(R_p)$ with a zero section) together with a proof $hD$ that $D$ represents, with Poincaré bundle, the rigidified line bundles on $\mathfrak X$ satisfying the fibrewise algebraic-equivalence-zero condition relative to `𝔛.εinf`; the corresponding datum $hDQ$ for the base change to $\mathbb Q$ and $hPQ$, an isomorphism between its Poincaré bundle and the base change of the pullback of $hD$'s Poincaré bundle; an Abel–Jacobi morphism $ajQ$ over $\mathbb Q$ sending the section `𝔛.εinf` to the zero section ($haj Q\varepsilon$) and satisfying, for every field $K$, every $t:\operatorname{Spec}K\to\operatorname{Spec}\mathbb Q$ and every point $x$ of the curve over $t$, the property $hajQ$ that the pullback of the Poincaré bundle along $x$ followed by $ajQ$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of $t$ followed by the base-changed `𝔛.εinf`; a comparison morphism $kQ$ from the geometric generic fibre to the $\mathbb Q$-fibre compatible with both projections ($hkQ_1$, $hkQ_2$, the latter over $\operatorname{Spec}\overline{\mathbb Q}\to\operatorname{Spec}\mathbb Q$); the composite $\overline{aj}=\mathfrak X.\mathrm{eeta}\mathbin{≫}kQ\mathbin{≫}ajQ\mathbin{≫}\mathrm{pr}_1$, a morphism $\mathfrak X.\mathrm{Meta}.C\to D.P$ lying over the generic point; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak X.\mathrm{Meta}.C$ whose image is `𝔛.εinf` and which $\overline{aj}$ carries to the zero section; and a bijection $\mathrm{pts}$ from $J_H = \mathrm{Pic}^0$ of `xHFunctionFieldBar M H` over $\overline{\mathbb Q}$ onto the $\overline{\mathbb Q}$-points of $D.\mathrm{toBase}$ which is additive for the relative group law attached to $hD$, equivariant for $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and which reads Abel–Jacobi on two-point differences: for all $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak X.\mathrm{Meta}.C$ with $s$ mapping to `𝔛.εinf`, there is a degree-zero divisor equal to $[\,\mathrm{place}(x)\,]-[\,\mathrm{place}(s)\,]$ whose class is sent by $\mathrm{pts}$ to $x$ followed by $\overline{aj}$. Let further $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho:R_p\to A$ be a ring homomorphism inducing the structure map $R_p\to\overline{\mathbb Q}$. Finally, let $i\in\{0,1\}$ and, for $n=1,2$, let $W_n$ be a place of `xHFunctionFieldBar M H` over $\overline{\mathbb Q}$, let $u_n$ be an $A$-point of $\mathfrak X$ over $\operatorname{Spec}\rho$ whose restriction to $\overline{\mathbb Q}$ is the point of the geometric generic fibre corresponding to $W_n$ under $\mathfrak X.\mathrm{Meta}$'s bijection between $\overline{\mathbb Q}$-points and places, and let $y_n$ be a section of the fibre of the model over the residue field of $A$ which is the reduction of $u_n$; assume the image of the closed point under $y_n$ lies in the range of the $i$-th component morphism $\mathfrak X.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,i$ and does not lie simultaneously in the ranges of the components $0$ and $1$. Assuming $[W_1]-[W_2]$ has degree zero, the conclusion is `ExtendsToPlace`: the $\overline{\mathbb Q}$-point $\mathrm{pts}$ of the class of $[W_1]-[W_2]$ in $\mathrm{Pic}^0$ factors as the canonical $\overline{\mathbb Q}$-point of $\operatorname{Spec}A$ followed by a section of $D.\mathrm{toBase}$ over $\operatorname{Spec}\rho$, i.e. it extends to an $A$-valued point of $D$.
--
--   This is the non-crossing, same-component case of the specialisation statement for the relative Picard functor of the model at $p\,\|\,M$: two places whose reductions lie on one and the same component of the geometric special fibre, neither at a crossing, give a difference class whose associated point of $\mathrm{Pic}^0$ is integral at $A$. It is used in the deduction of `extendsToPlace_pts_pic0Mk_of_forall_sum_filter_eq_zero`, where general degree-zero divisors with vanishing component-wise multidegrees are reduced to such pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_extendsToPlace_pts_pic0Mk_single_sub_single_of_mem_range_comp.lean

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

theorem ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_single_sub_single_of_mem_range_comp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
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

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (i : Fin 2)
    (W₁ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu₁ : Spec.map (CommRingCat.ofHom A.subtype) ≫ u₁.1 =
      ((𝔛.Meta.pointEquivPlace).symm W₁).1 ≫ 𝔛.eeta ≫
        pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    (y₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hy₁ : y₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
    (hy₁' : y₁ ≫ pullback.snd _ _ = 𝟙 _)
    (hc₁ : y₁.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ i).base)
    (hn₁ : ¬ (y₁.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
        y₁.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base))
    (W₂ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu₂ : Spec.map (CommRingCat.ofHom A.subtype) ≫ u₂.1 =
      ((𝔛.Meta.pointEquivPlace).symm W₂).1 ≫ 𝔛.eeta ≫
        pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    (y₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hy₂ : y₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
    (hy₂' : y₂ ≫ pullback.snd _ _ = 𝟙 _)
    (hc₂ : y₂.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ i).base)
    (hn₂ : ¬ (y₂.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
        y₂.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base))
    (hdeg : Finsupp.single W₁ (1 : ℤ) - Finsupp.single W₂ 1
      ∈ Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H))) :
    ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ)) (pts (Pic0.mk ⟨Finsupp.single W₁ (1 : ℤ) - Finsupp.single W₂ 1, hdeg⟩)) := by sorry
