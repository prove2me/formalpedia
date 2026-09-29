-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_mem_range_nodeUnit_of_isNodeUnitModule_poincare_pullbackAlong
-- name    : ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_mem_range_nodeUnit_of_isNodeUnitModule_poincare_pullbackAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/50f9923b-0158-50cf-9db5-e5032cff5c44
-- title:
--   Node-unit Poincaré bundle puts a special-fibre class in the toric part
-- statement:
--   Fix a prime $p$, a natural number $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$; fix a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$ and with algebraically closed residue field $\kappa$ of characteristic $p$, and assume the $q$-expansion $j(q)$ lies in the $q$-expansion function field of $SL(2,\mathbb{Z})$. Given a Deligne–Rapoport model $\mathfrak{X}$ at $p$ of level $(M,H)$, a level datum $\Lambda$ and a Néron object $O$ for $J_H(M)$ at $Pl$ over $\Lambda$, assume: the rigidified relative Picard functor of the level-$\Gamma_M$ model `toBase p (ΓM M H) hj` with section `𝔛.εinf`, restricted to the fibrewise algebraically trivial classes cut out by `algEquivZeroCut`, is represented by the designation with total space `O.G`, structure morphism `O.g` and zero section the unit point of `O.L` (`hrep`), and likewise the level-$\Gamma_N$ model with the section `𝔛.εinf` followed by `𝔛.π` is represented by the designation coming from $\Lambda$ (`hrepΛ`). Then for every ring homomorphism $\rho : R_p \to Pl$ lifting the structure map to $\overline{\mathbb{Q}}$, with $\Lambda.\sigma_A = \mathrm{Spec}\,\rho$, and making $\kappa$ an $R_p$-algebra via the residue map: given a representing datum $hD$ as in `hrep`, a representing datum $hD\kappa$ for the base change of that designation to $\kappa$ (with the section base-changed), an isomorphism of the Poincaré bundle of $hD\kappa$ with the $\kappa$-base change of the pullback of the Poincaré bundle of $hD$ along the first projection of `pullback O.g (specMap (R p) κ)`, the hypothesis `hc` that the two projections of the fibre product of the morphisms `𝔛.comp Pl hPl ρ hρ 0` and `𝔛.comp Pl hPl ρ hρ 1` (two morphisms from the $\kappa$-base change of the level-$\Gamma_N$ curve to that of the level-$\Gamma_M$ curve) have equal composites with the structure morphism of the former, a $Pl$-point $s$ of `O.G` over $\Lambda.\sigma_A$, a $\kappa$-point $y$ of the base-changed designation with $y$ followed by the first projection equal to `resPt Pl` followed by $s$, a family $w$ of units of $\kappa$ indexed by the $\kappa$-points of the crossing scheme, and the hypothesis that the pullback of the Poincaré bundle of $hD\kappa$ along $y$ is a node-unit module for the two components, the two families of crossing points obtained from the projections, and the units $(w j)^{-1}$ — that is, it admits maps to the pushforwards of the unit sheaves along the two components which are jointly injective on sections over each open with image exactly the pairs satisfying the node conditions for those units — the class $O.\mathrm{ptsSp}^{-1}$ of the $\kappa$-point `resPt Pl` followed by $s$ lies in the range of `GluedPic0.nodeUnit O.ssFinset`, the homomorphism sending a family of units indexed by the finset of pairs of places `O.ssFinset` to the glued class with both divisors zero and those gluing units.
--
--   This is the Mumford–Raynaud description of the toric part of the special fibre of $J_H(M)$ at a prime exactly dividing the level: a point of the Néron object over the residue field whose Poincaré bundle on the two-component special fibre of the Deligne–Rapoport model is trivial on each component and glued by prescribed units at the nodes is precisely the class produced by those units in the glued $\mathrm{Pic}^0$ group. It is used in the analysis of the inertia action at $p$ on points of the Néron object, through [`ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_smul_sub_eq_and_ptsSp_symm_mem_range_nodeUnit_of_mem_inertia_of_abelJacobiPins_of_representsRelSubPic`](thm.html#ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_smul_sub_eq_and_ptsSp_symm_mem_range_nodeUnit_of_mem_inertia_of_abelJacobiPins_of_representsRelSubPic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_mem_range_nodeUnit_of_isNodeUnitModule_poincare_pullbackAlong.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
  AlgebraicGeometry.TwoGluedCurves

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_mem_range_nodeUnit_of_isNodeUnitModule_poincare_pullbackAlong
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))    :
    ∀ (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ)),
    letI : Algebra (R p) (ResidueField ↥Pl) := ((IsLocalRing.residue ↥Pl).comp ρ).toAlgebra
    ∀ (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))
      (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥Pl)) (sectionBaseChange (ResidueField ↥Pl) 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥Pl)) (sectionBaseChange (ResidueField ↥Pl) 𝔛.εinf))
        (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange (ResidueField ↥Pl)))
      (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf (ResidueField ↥Pl)
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) (ResidueField ↥Pl)), pullback.condition⟩)).L))

      (hc : pullback.snd (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl)) = pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl)))

      (s : NeronModelInfra.SchemeHomOver Λ.σA O.g)
      (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl)))) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange (ResidueField ↥Pl)).toBase)
      (_ : y.1 ≫ pullback.fst O.g (specMap (R p) (ResidueField ↥Pl)) = ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ s.1)

      (w : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl)))) (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))) → Additive (ResidueField ↥Pl)ˣ)

      (_ : IsNodeUnitModule (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥Pl))
          (⟨(𝔛.comp Pl hPl ρ hρ 0), 𝔛.comp_over Pl hPl ρ hρ 0⟩ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl)) (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥Pl)))
          (⟨(𝔛.comp Pl hPl ρ hρ 1), 𝔛.comp_over Pl hPl ρ hρ 1⟩ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl)) (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥Pl)))
          (fun j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl)))) (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))) =>
            (⟨j.1 ≫ pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1), by rw [Category.assoc]; exact j.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl)))) (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))))
          (fun j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl)))) (pullback.fst (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))) =>
            (⟨j.1 ≫ pullback.snd (𝔛.comp Pl hPl ρ hρ 0) (𝔛.comp Pl hPl ρ hρ 1), by rw [Category.assoc, hc]; exact j.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl)))) (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥Pl))))
          (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl))))
          (fun j => Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField ↥Pl))).inv.hom.toMonoidHom (Additive.toMul (w j))⁻¹)
          (hDκ.poincare.pullbackAlong y).L),
      O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (ModularCurve.JZeroNeronObjectAtP.resPt Pl) rfl s) ∈
        (GluedPic0.nodeUnit O.ssFinset).range := by sorry
