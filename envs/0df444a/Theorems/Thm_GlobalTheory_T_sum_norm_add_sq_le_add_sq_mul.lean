-- Prove2me | Theorems.Thm_GlobalTheory_T_sum_norm_add_sq_le_add_sq_mul
-- name    : GlobalTheory.T.sum_norm_add_sq_le_add_sq_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:09.159972+00:00
-- url     : https://prove2.me/theorems/99c1972c-f79d-4154-b3cf-6e03ebcac76a
-- title:
--   T: sum norm add sq le add sq mul
-- statement:
--   The T construction uses the sum norm add sq le add sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumNormAddSqLeOfBoundsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumNormAddSqLeOfBoundsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormAddSqLeOfBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormAddSqLeOfBoundsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sum_norm_add_sq_le_add_sq_mul : ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by sorry
