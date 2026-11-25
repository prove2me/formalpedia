-- Prove2me | Theorems.Thm_GlobalTheory_sum_prod_box_erase_zero
-- name    : GlobalTheory.sum_prod_box_erase_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:34:40.031124+00:00
-- url     : https://prove2.me/theorems/c6688c96-6276-4224-a63d-e87a9ddf312c
-- title:
--   Global Theory: sum prod box erase zero
-- statement:
--   The Global Theory construction uses the sum prod box erase zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDyadicShellIndex.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDyadicShellIndex.lean#L20-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ShellSumElementaryInequalities
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDyadicShellIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory

theorem GlobalTheory.sum_prod_box_erase_zero (ι : Type) [Fintype ι] [DecidableEq ι] (W : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ (Fintype.piFinset (fun _ : ι => range (N + 1))).erase (fun _ => 0), ∏ v, W (k v)
      = (W 0 + ∑ i ∈ range N, W (i + 1)) ^ Fintype.card ι - W 0 ^ Fintype.card ι := by sorry
