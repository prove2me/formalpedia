-- Prove2me | Theorems.Thm_ModularCurve_exists_schemeHomOver_pts_smul_sub_eq_and_ptsSp_symm_mem_range_nodeUnit_of_mem_inertia_jHNeronObjectAtP
-- name    : ModularCurve.exists_schemeHomOver_pts_smul_sub_eq_and_ptsSp_symm_mem_range_nodeUnit_of_mem_inertia_jHNeronObjectAtP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/566eb0d4-061c-5e7a-9717-463555341047
-- title:
--   Inertia differences on J_H reduce to node units
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$, with $M/p$ nonzero; let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$ (so $Pl$ lies over $p$) whose residue field is algebraically closed of characteristic $p$. Assume the Laurent expansion `jqModC` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤`, and fix: a model datum $\mathfrak{X}$ of type `XHDRModelAtP p M H hpM hj`; level data $\Lambda$ (a morphism $\sigma_A : \operatorname{Spec} Pl \to$ `base p` lifting the generic point, a scheme $\Lambda.X$ over `base p` with a relative group law and dictionaries for points at level $M/p$); and a Néron object $O$ for $J_H(M)$ over $Pl$ (a smooth, separated, surjective $G \to$ `base p` with commutative relative group law, a group isomorphism `O.pts` from `JH M H` onto the sections over the generic point, Hecke correspondences, and the further properties recorded in `JHNeronObjectAtP`). Assume moreover that $(O.G, O.g)$ with the identity section of its group law represents the functor of rigidified line bundles on `toBase p (ΓM M H) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ that are fibrewise algebraically equivalent to zero, and that $(\Lambda.X, \Lambda.f)$ likewise represents the corresponding functor for `toBase p (ΓN p M H hpM) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$. Then for every $\sigma$ in the inertia subgroup of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ attached to $Pl$ (the image of the inertia subgroup inside the decomposition subgroup) and every $x \in$ `JH M H` there is a morphism $s : \operatorname{Spec} Pl \to O.G$ with $s \circ O.g = \Lambda.\sigma_A$ such that the $\overline{\mathbb{Q}}$-point of $O.G$ attached by `O.pts` to $\sigma \cdot x - x$ equals $s$ precomposed with $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec} Pl$, and such that the restriction of $s$ along $\operatorname{Spec}$ of the residue map, read backwards through the special dictionary `O.ptsSp`, lies in the image of the homomorphism `GluedPic0.nodeUnit O.ssFinset`, which sends a family of units indexed by the finite set of pairs of places `O.ssFinset` to the class of the gluing datum with both divisor components zero.
--
--   This is the local statement at $p$ that, for $p$ exactly dividing the level, inertia at a place above $p$ moves a point of $J_H(M)$ only within the toric part: the difference $\sigma x - x$ extends to a section of the Néron object over the valuation ring and its reduction is a pure gluing datum of the two components of the special fibre of the Deligne–Rapoport model. It is the form in which the statement is used by the lemmas placing such differences in the toric points of $J_H$, which feed the level-lowering argument at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_schemeHomOver_pts_smul_sub_eq_and_ptsSp_symm_mem_range_nodeUnit_of_mem_inertia_jHNeronObjectAtP.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.exists_schemeHomOver_pts_smul_sub_eq_and_ptsSp_symm_mem_range_nodeUnit_of_mem_inertia_jHNeronObjectAtP
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
    ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ x : ModularCurve.JH M H,
      ∃ s : NeronModelInfra.SchemeHomOver Λ.σA O.g,
        (O.pts (σ • x - x)).1 = ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (ModularCurve.JZeroNeronObjectAtP.resPt Pl) rfl s) ∈
          (GluedPic0.nodeUnit O.ssFinset).range := by sorry
