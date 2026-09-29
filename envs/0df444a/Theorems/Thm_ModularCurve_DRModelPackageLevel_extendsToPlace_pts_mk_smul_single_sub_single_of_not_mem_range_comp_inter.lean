-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter
-- name    : ModularCurve.DRModelPackageLevel.extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/84f0d3d9-0224-5292-903e-04c629f6ad61
-- title:
--   Inertia displacement at a non-crossing point extends to A
-- statement:
--   Fix a prime $p$ and a nonzero $N_0$ with $p\nmid N_0$, let $\mathfrak P$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀` for level $N_0p$, and assume `toBase N₀ p` (the model over `R p`) is proper. The data are: a designation $D$ (a scheme $D.P$ over $\operatorname{Spec}(R_p)$ with a section `zeroSection`); a witness $hD$ that $D$ represents the functor of line bundles rigidified along $\mathfrak P.\varepsilon_{\inf}$ that are fibrewise algebraically equivalent to zero; the analogous witness $hDQ$ after base change to $\mathbb Q$, together with $hPQ$, an isomorphism of its Poincaré bundle with the base change of that of $hD$; an Abel–Jacobi morphism $ajQ$ over $\mathbb Q$ from the generic-fibre curve to $D_{\mathbb Q}$ carrying the cusp section to the zero section ($hajQ\varepsilon$) and satisfying $hajQ$: for every field $K$, every $t:\operatorname{Spec}K\to\operatorname{Spec}\mathbb Q$ and every point $x$ over $t$, the pullback of the Poincaré bundle along $x$ followed by $ajQ$ is isomorphic to the line bundle of the Cartier divisor of $x$ tensored with the ideal module of the cusp at $t$; a morphism $kQ$ from the geometric generic fibre to the $\mathbb Q$-fibre compatible with both projections ($hkQ_1$, $hkQ_2$, the latter through $\mathbb Q\to\overline{\mathbb Q}$); the composite $\overline{aj}=\mathfrak P.eeta\circ kQ$ followed by $ajQ$ and the first projection, lying over `genPt p`; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak P.\mathrm{Meta}.C$ which is the cusp and is sent to the zero section by $\overline{aj}$; and a bijection $pts$ from $\mathrm{Pic}^0$ of the function field $\overline{\mathbb Q}$-curve of level $N_0p$ to the $\overline{\mathbb Q}$-points of $D.toBase$, additive for the relative group law supplied by $hD$, equivariant for $\operatorname{Aut}(\overline{\mathbb Q}/\mathbb Q)$, and Abel–Jacobi compatible: for points $x,s$ with $s$ the cusp, the class of $[\text{place of }x]-[\text{place of }s]$ is sent to $x$ followed by $\overline{aj}$. Let finally $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ in its nonunits, and $\rho:R_p\to A$ inducing the structure map to $\overline{\mathbb Q}$. The assertion: for every place $V$ of the function field, every section $s$ of `toBase N₀ p` over $\operatorname{Spec}\rho$ whose base change to $\overline{\mathbb Q}$ is the point attached to $V$ by $\mathfrak P.\mathrm{Meta}.pointEquivPlace$, and every $y$ over the residue field of $A$ with $y$ a section of the special fibre reducing $s$, if the image of $y$ is not contained in both of the ranges of $\mathfrak P.comp\,\dots\,0$ and $\mathfrak P.comp\,\dots\,1$, then for each $\sigma$ in the inertia subgroup of $A$ over $\mathbb Q$ and each proof that $\sigma\cdot[V]-[V]$ has degree zero, the point $pts$ of the class of $\sigma\cdot[V]-[V]$ satisfies `ExtendsToPlace A (Spec.map ρ)`, i.e. it factors through a section of $D.toBase$ over $\operatorname{Spec}A$.
--
--   This is the smooth-point case of Raynaud's Picard-functor argument that inertia moves a point of the Jacobian into the identity component of the Néron model: when the specialisation of the $A$-section attached to $V$ avoids the crossings of the two components of the Deligne–Rapoport special fibre, the divisor $\overline{\sigma V}-\overline{V}$ is relatively Cartier of fibrewise degree zero and so defines an $A$-point of the relative Picard scheme. It is used by [`ModularCurve.DRModelPackageLevel.extendsToPlace_pts_smul_sub`](thm.html#ModularCurve.DRModelPackageLevel.extendsToPlace_pts_smul_sub), on the way to the semistability and component-group input of the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter.lean

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
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter
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

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_hs : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
        ((𝔓.Meta.pointEquivPlace).symm V).1 ≫ 𝔓.eeta ≫
          pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))))
      (y : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
      (_hy₁ : y ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1)
      (_hy₂ : y ≫ pullback.snd _ _ = 𝟙 _),
      ¬ (Set.range y.base ⊆ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) 0).base ∧
          Set.range y.base ⊆ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) 1).base) →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ,
          ∀ (hdeg : arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1
              ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))),
            ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ))
              (pts (Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • (Finsupp.single V (1 : ℤ))
                - Finsupp.single V 1, hdeg⟩)) := by sorry
