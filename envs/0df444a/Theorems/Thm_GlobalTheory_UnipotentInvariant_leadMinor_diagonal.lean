-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentInvariant_leadMinor_diagonal
-- name    : GlobalTheory.UnipotentInvariant.leadMinor_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:39.998851+00:00
-- url     : https://prove2.me/theorems/46e4725c-e5aa-49e5-9212-19b2c58df2b4
-- title:
--   Unipotent Invariant: lead Minor diagonal
-- statement:
--   The Unipotent Invariant construction uses the lead Minor diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L185-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L185-L204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}

theorem GlobalTheory.UnipotentInvariant.leadMinor_diagonal (i : Fin p) (d : Fin p → K) :
    leadMinor i (diagonal d) = ∏ a ∈ Finset.Iic i, d a := by sorry
