-- Prove2me | Theorems.Thm_GlobalTheory_abs_lowK_sub_le
-- name    : GlobalTheory.abs_lowK_sub_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:10.360414+00:00
-- url     : https://prove2.me/theorems/46402d96-c2e7-4aa8-a5e4-38417c519745
-- title:
--   Global Theory: abs low K sub le
-- statement:
--   The Global Theory construction uses the abs low K sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CardFilterFinBounds.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CardFilterFinBounds.lean#L15-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterFinBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.abs_lowK_sub_le {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (a : Fin n) :
    -(n : ℝ) ≤ lowK ε μ a - μ a ∧ lowK ε μ a - μ a ≤ n := by sorry
