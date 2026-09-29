-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_extendsToPlace_pts_mk_smul_single_sub_single_of_range_subset_range_comp_inter
-- name    : ModularCurve.XHDRModelAtP.extendsToPlace_pts_mk_smul_single_sub_single_of_range_subset_range_comp_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/16df84af-1a52-593d-9e6b-31c5b701823b
-- title:
--   Inertial displacement of a place extends: crossing case
-- statement:
--   Fix a prime $p$ and $M>0$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^{\times}$, and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` lies in the full-level $q$-expansion field; let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj`, whose data include a model of $X_H$ over $R_p$ with properness, flatness, integrality and normality, and a `CurveModel` $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` identified by `eeta` with the geometric generic fibre. Further data, listed as hypotheses: a relative $\mathrm{Pic}^0$ designation $D$ over $R_p$ representing, via `hD`, the sub-Picard condition of fibrewise algebraically trivial rigidified line bundles with rigidification $\mathfrak{X}.\varepsilon_{\inf}$; its counterpart `hDQ` over $\mathbb{Q}$ together with an isomorphism `hPQ` of Poincaré bundles; an Abel–Jacobi morphism `ajQ` over $\mathbb{Q}$ killing the section and computing, on points over any field, the class $[x]-[\varepsilon]$; a comparison morphism `kQ` of generic fibres; the induced $\overline{\mathbb{Q}}$-morphism `ajbar` with base point `εbar`; and a bijection `pts` from $J_H = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \mathrm{xHFunctionFieldBar}\,M\,H)$ to the $\overline{\mathbb{Q}}$-points of $D$ that is additive for the relative group law of `hD`, Galois-equivariant, and compatible with `ajbar` on differences of places. Let $A \subset \overline{\mathbb{Q}}$ be a valuation subring with $p$ a non-unit, with algebraically closed residue field of characteristic $p$, and $\rho : R_p \to A$ a lift of $R_p \to \overline{\mathbb{Q}}$. Let $V$ be a place of `xHFunctionFieldBar M H`, let $s$ be an $A$-point of the model over $\mathrm{Spec}\,\rho$ whose generic fibre is the $\overline{\mathbb{Q}}$-point corresponding to $V$ under `𝔛.Meta.pointEquivPlace`, and let $y$ be a section of the special fibre over the residue field of $A$ reducing $s$. Assume the crossing hypothesis that the image of $y$ is contained in the images of both `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1`. Finally let $\sigma$ lie in the inertia subgroup of $A$ inside $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$, and assume $\sigma \cdot [V] - [V]$ has degree zero, the Galois action on places being `arithmeticGalois`. The conclusion is `ExtendsToPlace`: the $\overline{\mathbb{Q}}$-point `pts` of the class of $\sigma \cdot [V] - [V]$ in $\mathrm{Pic}^0$ factors as `barPt A` followed by some $A$-point of $D$ over $\mathrm{Spec}\,\rho$.
--
--   This is the crossing-point case of the assertion that, for a place $V$ of the geometric modular curve whose $A$-integral point reduces to a point lying on both distinguished components of the special fibre, the inertial displacement $[\sigma V] - [V]$ defines a point of the Jacobian with values in the valuation ring $A$ rather than only in $\overline{\mathbb{Q}}$. It is combined with the corresponding smooth-reduction case in [`ModularCurve.XHDRModelAtP.extendsToPlace_pts_smul_sub_of_mem_inertiaSubgroupIn`](thm.html#ModularCurve.XHDRModelAtP.extendsToPlace_pts_smul_sub_of_mem_inertiaSubgroupIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_extendsToPlace_pts_mk_smul_single_sub_single_of_range_subset_range_comp_inter.lean

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

set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.extendsToPlace_pts_mk_smul_single_sub_single_of_range_subset_range_comp_inter
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
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

    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hs : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
      ((𝔛.Meta.pointEquivPlace).symm V).1 ≫ 𝔛.eeta ≫
        pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    (y : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hy₁ : y ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1)
    (hy₂ : y ≫ pullback.snd _ _ = 𝟙 _)

    (hc : (Set.range y.base ⊆ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
        Set.range y.base ⊆ Set.range (𝔛.comp A hA ρ hρ 1).base))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (hdeg : arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) σ • (Finsupp.single V (1 : ℤ)) - Finsupp.single V 1
      ∈ Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H))) :
    ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ))
      (pts (Pic0.mk ⟨arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) σ • (Finsupp.single V (1 : ℤ)) - Finsupp.single V 1, hdeg⟩)) := by sorry
