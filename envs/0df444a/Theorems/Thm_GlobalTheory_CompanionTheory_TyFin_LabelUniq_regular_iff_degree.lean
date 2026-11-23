-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_regular_iff_degree
-- name    : GlobalTheory.CompanionTheory.TyFin.LabelUniq.regular_iff_degree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:28:30.7353+00:00
-- url     : https://prove2.me/theorems/9cf01bbf-f91a-4df2-a596-565e1ae0b676
-- title:
--   Label Uniq: regular iff degree
-- statement:
--   The Label Uniq construction uses the regular iff degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean#L118-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean#L118-L161

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.LabelUniq
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem GlobalTheory.CompanionTheory.TyFin.LabelUniq.regular_iff_degree {d : ℕ} (hd : 0 < d) (α : AlgebraicClosure K)
    (hα : α ^ (Fintype.card K ^ d - 1) = 1) :
    ((∀ e : ℕ, 0 < e → e < d → α ^ Fintype.card K ^ e ≠ α) ↔ (minpoly K α).natDegree = d) ∧
      ((minpoly K α).natDegree = d →
        ∃ x : GL (Fin d) K, Matrix.charpoly (x : Matrix (Fin d) (Fin d) K) = minpoly K α) := by sorry
