-- Prove2me | Theorems.Thm_GlobalTheory_LowCasShift_sq_le_nsq
-- name    : GlobalTheory.LowCasShift.sq_le_nsq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:05.126838+00:00
-- url     : https://prove2.me/theorems/fa10c63a-b236-4f17-9321-7fb3cb387d36
-- title:
--   Low Cas Shift: sq le nsq
-- statement:
--   The Low Cas Shift construction uses the sq le nsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLe.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLe.lean#L53-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LowKSubSingleSqrtCkvLe
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
open GlobalTheory GlobalTheory.LowCasShift

theorem GlobalTheory.LowCasShift.sq_le_nsq {n : ℕ} (u : Fin n → ℝ) (a : Fin n) : u a * u a ≤ nsq u := by sorry
