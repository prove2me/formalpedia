-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_pts_eq_barPt_comp_and_ptsSp_symm_eq_of_smul_eq_zero_of_abelianScheme
-- name    : ModularCurve.JHNeronObjectAtP.LevelData.exists_pts_eq_barPt_comp_and_ptsSp_symm_eq_of_smul_eq_zero_of_abelianScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/622e7dec-bf19-503e-9d31-21c70756e655
-- title:
--   Lifting p^k-torsion along a level-(M/p) Néron datum
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $p \mid M$ and $M/p \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field is algebraically closed of characteristic $p$. Let $\Lambda$ be a `LevelData` at $A$: a structure morphism $\sigma_A : \operatorname{Spec} A \to \operatorname{Spec}(\mathbb{Q}\text{-integers with denominator coprime to } p)$ with `barPt A` followed by $\sigma_A$ equal to `genPt p`, a scheme $\Lambda.X$ with a morphism $\Lambda.f$ to that base, a relative group law $\Lambda.L$ on $\Lambda.f$, and bijections $\Lambda.\mathrm{pts}$ from $\mathrm{Pic}^0$ of the base-changed function field of $X_H$ at level $M/p$ and $H$'s image in $(\mathbb{Z}/(M/p))^{\times}$ onto the sections over `genPt p`, and $\Lambda.\mathrm{ptsSp}$ from $\mathrm{Pic}^0$ of the residue-field $q$-expansion function field onto the sections over `resPt A` followed by $\sigma_A$. Assume $\Lambda.f$ is smooth and proper with connected fibres and admits a relative group law, and that both bijections are additive for $\Lambda.L$ (the special one via the group law base-changed along `resPt A` followed by $\sigma_A$). Then for each $k$ and each degree-zero class $z$ with $p^k z = 0$ there are $x$ with $p^k x = 0$ and a section $s$ of $\Lambda.f$ over $\sigma_A$ such that $(\Lambda.\mathrm{pts}\,x).1$ is `barPt A` followed by $s.1$, and $\Lambda.\mathrm{ptsSp}^{-1}$ of (`resPt A` followed by $s.1$) is $z$.
--
--   This is the surjectivity of reduction on $p^k$-torsion for the abelian scheme attached to the level-$(M/p)$ datum over a place of $\overline{\mathbb{Q}}$ above $p$: every $p^k$-torsion class on the special fibre is the reduction of a $p^k$-torsion point that extends over the valuation ring. It is used in the construction of the Néron object at $p$ at level $(M,H)$, by [`ModularCurve.JHNeronObjectAtP.exists_eq_add_pull_add_pull_of_mem_finPts_of_abelJacobiPin`](thm.html#ModularCurve.JHNeronObjectAtP.exists_eq_add_pull_add_pull_of_mem_finPts_of_abelJacobiPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_pts_eq_barPt_comp_and_ptsSp_symm_eq_of_smul_eq_zero_of_abelianScheme.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_ModularCurve_XHDiamondModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.LevelData.exists_pts_eq_barPt_comp_and_ptsSp_symm_eq_of_smul_eq_zero_of_abelianScheme
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (k : ℕ) :
    ∀ z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), (p ^ k : ℤ) • z = 0 →
      ∃ (x : JH (M / p) (infSubgroup p M H hpM)) (s : NeronModelInfra.SchemeHomOver Λ.σA Λ.f),
        (p ^ k : ℤ) • x = 0 ∧ (Λ.pts x).1 = barPt A ≫ s.1 ∧
        Λ.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s) = z := by sorry
