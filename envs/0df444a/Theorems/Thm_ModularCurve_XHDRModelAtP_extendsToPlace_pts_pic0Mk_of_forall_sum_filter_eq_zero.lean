-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_extendsToPlace_pts_pic0Mk_of_forall_sum_filter_eq_zero
-- name    : ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_of_forall_sum_filter_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/8fdd0760-1551-5d0e-b392-3985d749ea77
-- title:
--   Bidegree (0,0) divisor classes extend to A-points
-- statement:
--   Fix a prime $p$ and a natural number $M \neq 0$ with $p \mid M$ and $p^{2} \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and the hypothesis `hj` that `jqModC ℚ` lies in the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj`, so in particular a proper flat integral model `toBase p (ΓM M H) hj` over $\operatorname{Spec}(R\,p)$ together with a curve model `𝔛.Meta` of the geometric function field `xHFunctionFieldBar M H`, an isomorphism `𝔛.eeta` onto the base change of the model to $\overline{\mathbb{Q}}$, and a section `𝔛.εinf`. Let $D$ be a `RelativePic0Designation` for this model, i.e. a scheme $D.P$ over $\operatorname{Spec}(R\,p)$ with a zero section, and assume: $D$, respectively its base change to $\mathbb{Q}$, represents the relative rigidified Picard functor cut out by the fibrewise algebraically trivial condition `algEquivZeroCut` (hypotheses `hD`, `hDQ`), the two Poincaré bundles agree under base change (`hPQ`), there is an Abel–Jacobi morphism `ajQ` over $\mathbb{Q}$ killing the section `𝔛.εinf` and satisfying, for every field $K$ and every $K$-point $x$, that the pullback of the Poincaré bundle along $x$ followed by `ajQ` is the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the $\varepsilon$-section (`hajQ`), a comparison morphism `kQ` between the pullback along the geometric generic point and along $\operatorname{Spec}\mathbb{Q}$ commuting with both projections, the induced morphism `ajbar` from `𝔛.Meta.C` to $D.P$ over the generic point, a geometric base point `εbar` mapping to `𝔛.εinf` and to the zero section, and a bijection `pts` from $J_H = \mathrm{Pic}^{0}$ of `xHFunctionFieldBar M H` onto the sections of $D.toBase$ over the geometric generic point which is additive for the relative group law given by `hD`, Galois-equivariant, and compatible with `ajbar` in the sense that for geometric points $x$ and $s$ with $s$ over `𝔛.εinf` there is a degree-zero divisor equal to $[\,\text{place of }x\,] - [\,\text{place of }s\,]$ whose class is sent by `pts` to $x$ followed by `ajbar`. Let further $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its non-units, with algebraically closed residue field of characteristic $p$, and let $\rho : R\,p \to A$ be a ring homomorphism inducing the structure map to $\overline{\mathbb{Q}}$. Given $n$, places $W_{0},\dots,W_{n-1}$ of `xHFunctionFieldBar M H`, labels $c_i \in \{0,1\}$ and the hypothesis `hgood` that for each $i$ every $A$-point of the model over $\operatorname{Spec}\rho$ whose geometric fibre is the point attached to $W_i$ by `𝔛.Meta.pointEquivPlace` and `𝔛.eeta` has the property that every residue-field section of the special fibre reducing it carries the closed point into the image of `𝔛.comp A hA ρ hρ (c i)` and not simultaneously into the images of `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1`, and integers $m_i$ with $\sum_{c_i = j} m_i = 0$ for $j = 0, 1$, let $D_x$ be a degree-zero divisor equal to $\sum_i m_i [W_i]$. Then `pts` of the class of $D_x$ satisfies `ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ))`, that is, it factors as the geometric point `barPt A` followed by a section of $D.toBase$ over $\operatorname{Spec}\rho$.
--
--   This is the sufficiency half of Raynaud's description of the identity component of the Néron model of $J_H(M)$ at a prime exactly dividing the level: a divisor class of degree zero on each of the two components of the special fibre of the Deligne–Rapoport model, supported at places reducing to smooth points, specialises to an $A$-integral point of the representing scheme of the relative $\mathrm{Pic}^{0}$. It is reduced to the case of a difference of two places on one component, and is used in the construction of the Néron-model data for $J_H$ at $p$ by [`ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_forall_dvd_ord_residue_of_abelJacobiPin_offDiag_of_wgen`](thm.html#ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_forall_dvd_ord_residue_of_abelJacobiPin_offDiag_of_wgen) and [`ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_isGoodClass_of_abelJacobiPin_offDiag`](thm.html#ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_isGoodClass_of_abelJacobiPin_offDiag).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_extendsToPlace_pts_pic0Mk_of_forall_sum_filter_eq_zero.lean

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

theorem ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_of_forall_sum_filter_eq_zero
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

    {n : ℕ} (W : Fin n → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (c : Fin n → Fin 2)
    (hgood : ∀ (i : Fin n) (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 =
        ((𝔛.Meta.pointEquivPlace).symm (W i)).1 ≫ 𝔛.eeta ≫
          pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) →
      ∀ (yκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
        yκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 → yκ ≫ pullback.snd _ _ = 𝟙 _ →
        yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ (c i)).base ∧
        ¬ (yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
            yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base))
    (m : Fin n → ℤ)
    (hdeg : ∀ j : Fin 2, (∑ i ∈ Finset.univ.filter (fun i => c i = j), m i) = 0)
    (Dx : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hDx : (Dx : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = ∑ i, Finsupp.single (W i) (m i)) :
    ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ)) (pts (Pic0.mk Dx)) := by sorry
