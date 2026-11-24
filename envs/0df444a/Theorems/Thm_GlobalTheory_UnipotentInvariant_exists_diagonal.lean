-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentInvariant_exists_diagonal
-- name    : GlobalTheory.UnipotentInvariant.exists_diagonal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:25:30.464796+00:00
-- url     : https://prove2.me/theorems/6f057af0-3d83-4bb6-86aa-78ebe2cca7bd
-- title:
--   Unipotent Invariant: exists diagonal
-- statement:
--   The Unipotent Invariant construction uses the exists diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L173-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L173-L183

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

theorem GlobalTheory.UnipotentInvariant.exists_diagonal (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) :
    ∃ d : Fin p → K, ∀ f, BiInvariant f → f (diagonal d) = f M := by sorry
