-- Prove2me | Theorems.Thm_ModularCurve_regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN
-- name    : ModularCurve.regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/64fba408-087d-5532-89bf-aebee2608bef
-- title:
--   Uniqueness of the regular prolongation reducing j and j_M
-- statement:
--   Let $M\ge 1$ and let $q$ be a prime not dividing $M$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that the image of $q$ is a nonunit of $A$, and write $\kappa$ for its residue field. Let $S,S'$ be intermediate fields of $\kappa((q))/\kappa$, both equal to $\kappa$-adjoin$\{\tilde j,\tilde j_M\}$, where $\tilde j = q^{-1}\cdot(E_4^3\eta^{-24}$ reduced to $\kappa)$ and $\tilde j_M$ is its image under $q\mapsto q^M$. Let $R$ and $R'$ be regular prolongations of $A$ to $F=\overline{\mathbb{Q}}$-adjoin of the coefficientwise images of $\mathbb{Q}$-adjoin$(\mathrm{divisorExpansions}\,M)$ inside $\overline{\mathbb{Q}}((q))$, with residue fields $S$, $S'$ respectively: that is, valuation subrings of $F$ contracting to $A$ along $\overline{\mathbb{Q}}\to F$, with surjective residue maps whose kernels are the maximal ideals, compatible with the residue map of $A$, and such that every nonzero element of $F$ has an $\overline{\mathbb{Q}}$-multiple lying in the ring with nonzero residue. Assume that the coefficientwise images of $j$ and of $j(q^M)$ lie in the integers of both $R$ and $R'$, with residues $\tilde j$ and $\tilde j_M$ in $\kappa((q))$. Then $R$ and $R'$ have the same ring of integers, and for every $f$ in that ring the two residues agree in $\kappa((q))$.
--
--   This is the rigidity, or uniqueness, of the constant reduction of $X_0(M)$ at a prime $q$ of good reduction, expressed in the language of regular prolongations: the reduction is determined by the prescribed residues of $j$ and $j(q^M)$. It is used in the comparison of the Hecke correspondences on $X_0(M)$ with their specialisations, via [`ModularCurve.PlaceSpecialization.restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

theorem ModularCurve.regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN
    (M q : ℕ) [NeZero M] (hq : q.Prime) (hqM : ¬ q ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {S S' : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))}
    (hS : S = modularFunctionFieldC (ResidueField ↥A) M)
    (hS' : S' = modularFunctionFieldC (ResidueField ↥A) M)
    (R : RegularProlongation A (modularFunctionFieldBar M) S)
    (R' : RegularProlongation A (modularFunctionFieldBar M) S')
    (hj : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full M (jq_mem M))⟩ : modularFunctionFieldBar M)
        ∈ R.integers,
      (R.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (hjM : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full M (dvd_refl M))⟩ : modularFunctionFieldBar M)
        ∈ R.integers,
      (R.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqNModC (ResidueField ↥A) M)
    (hj' : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full M (jq_mem M))⟩ : modularFunctionFieldBar M)
        ∈ R'.integers,
      (R'.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (hjM' : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full M (dvd_refl M))⟩ : modularFunctionFieldBar M)
        ∈ R'.integers,
      (R'.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqNModC (ResidueField ↥A) M) :
    R.integers = R'.integers ∧
      ∀ (f : modularFunctionFieldBar M) (h : f ∈ R.integers) (h' : f ∈ R'.integers),
        (R.residue ⟨f, h⟩ : LaurentSeries (ResidueField ↥A))
          = (R'.residue ⟨f, h'⟩ : LaurentSeries (ResidueField ↥A)) := by sorry
