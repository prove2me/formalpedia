-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_section_mul_inv_one_and_ptsSp_symm_eq
-- name    : ModularCurve.JHNeronObjectAtP.exists_section_mul_inv_one_and_ptsSp_symm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/d2f01a16-edce-5729-baa5-fefe0df8abb5
-- title:
--   Group law, reduction and rigidity for A-sections of G
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, with residue field algebraically closed of characteristic $p$; fix further a level datum $\Lambda$ of type `JHNeronObjectAtP.LevelData p M H hpM A`, providing in particular a structure morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec}(\mathtt{baseRing } p)$ whose restriction `barPt A` $\!\circ\!$-composite is the generic point, and an object $O$ of type `JHNeronObjectAtP p M H hpM A hA Λ`, consisting of a scheme $G$ with structure morphism $g \colon G \to \operatorname{Spec}(\mathtt{baseRing } p)$, a relative group law `O.L` on $g$, a bijection `O.pts` from $J_H(M) = \operatorname{Pic}^0$ of the function field of $X_H(M)$ over $\overline{\mathbb{Q}}$ onto the sections of $g$ over the generic point, and a bijection `O.ptsSp` from a group of divisor classes over the residue field of $A$ onto the sections of $g$ over $\operatorname{resPt} A$ followed by $\sigma_A$. Call $s$ an $A$-section if $s \colon \operatorname{Spec} A \to G$ satisfies $s \circ\!$-compatibility $s.1 \gg\!= \sigma_A$, write $\bar{s} = \operatorname{barPt} A$ followed by $s.1$ for its generic fibre, and $\operatorname{red}(s) =$ `O.ptsSp.symm` applied to $\operatorname{resPt} A$ followed by $s.1$ for its reduction class. The conclusion is the conjunction of five assertions: (i) for all $x, y \in J_H(M)$ and all $A$-sections $s, t$ with $\overline{(\mathtt{O.pts } x)} = \bar{s}$ and $\overline{(\mathtt{O.pts } y)} = \bar{t}$, the generic fibre of `O.pts (x + y)` is that of `O.L.mul Λ.σA s t` and $\operatorname{red}(\mathtt{O.L.mul Λ.σA } s\, t) = \operatorname{red}(s) + \operatorname{red}(t)$; (ii) likewise for all $x$ and $s$ with $\overline{(\mathtt{O.pts } x)} = \bar{s}$, the section `O.L.inv Λ.σA s` has generic fibre that of `O.pts (-x)` and reduction $-\operatorname{red}(s)$; (iii) the unit section `O.L.one Λ.σA` has generic fibre that of `O.pts 0` and reduction $0$; (iv) for every $A$-section $s$, $\operatorname{red}(s) = 0$ if and only if $\operatorname{resPt} A$ followed by $s.1$ equals the base change along $\operatorname{resPt} A$ followed by $\sigma_A$ of the unit section `O.L.one (𝟙 (base p))`; (v) two $A$-sections with the same generic fibre are equal.
--
--   This packages the interaction, over the valuation ring $A$, between the relative group law on the Néron object $G$ attached to $J_H(M)$ at $p$, the dictionary of $\overline{\mathbb{Q}}$-points and the dictionary of points of the special fibre: $A$-sections extending given generic points may be added, negated and reduced compatibly, the reduction of a section vanishes exactly when it agrees with the unit section on the special fibre, and an $A$-section is determined by its generic fibre (the uniqueness half of the valuative criterion of separatedness). It is used by [`ModularCurve.JHNeronObjectAtP.exists_eq_add_pull_add_pull_of_mem_finPts_of_abelJacobiPin`](thm.html#ModularCurve.JHNeronObjectAtP.exists_eq_add_pull_add_pull_of_mem_finPts_of_abelJacobiPin), where a class in the special fibre is decomposed using sections that extend prescribed generic points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_section_mul_inv_one_and_ptsSp_symm_eq.lean

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

theorem ModularCurve.JHNeronObjectAtP.exists_section_mul_inv_one_and_ptsSp_symm_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) :

    (∀ (x y : JH M H) (s t : NeronModelInfra.SchemeHomOver Λ.σA O.g),
      (O.pts x).1 = barPt A ≫ s.1 → (O.pts y).1 = barPt A ≫ t.1 →
        (O.pts (x + y)).1 = barPt A ≫ (O.L.mul Λ.σA s t).1 ∧
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.mul Λ.σA s t)) =
          O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s) +
            O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ t)) ∧

    (∀ (x : JH M H) (s : NeronModelInfra.SchemeHomOver Λ.σA O.g),
      (O.pts x).1 = barPt A ≫ s.1 →
        (O.pts (-x)).1 = barPt A ≫ (O.L.inv Λ.σA s).1 ∧
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.inv Λ.σA s)) =
          - O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s)) ∧

    ((O.pts 0).1 = barPt A ≫ (O.L.one Λ.σA).1 ∧
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.one Λ.σA)) = 0) ∧

    (∀ s : NeronModelInfra.SchemeHomOver Λ.σA O.g,
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s) = 0 ↔
        resPt A ≫ s.1 = (resPt A ≫ Λ.σA) ≫ (O.L.one (𝟙 (base p))).1) ∧

    (∀ s t : NeronModelInfra.SchemeHomOver Λ.σA O.g, barPt A ≫ s.1 = barPt A ≫ t.1 → s = t) := by sorry
