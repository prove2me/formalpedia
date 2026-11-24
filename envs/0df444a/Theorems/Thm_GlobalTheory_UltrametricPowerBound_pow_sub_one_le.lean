-- Prove2me | Theorems.Thm_GlobalTheory_UltrametricPowerBound_pow_sub_one_le
-- name    : GlobalTheory.UltrametricPowerBound.pow_sub_one_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:23:18.677208+00:00
-- url     : https://prove2.me/theorems/aedf566a-a804-413e-85bd-564bd0caf0fc
-- title:
--   Ultrametric Power Bound: pow sub one le
-- statement:
--   The Ultrametric Power Bound construction uses the pow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubOneLe.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubOneLe.lean#L9-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UltrametricPowerBound
variable {l : ℕ} [Fact (Nat.Prime l)]

theorem GlobalTheory.UltrametricPowerBound.pow_sub_one_le (w : ℚ_[l]) (hw : ‖w‖ ≤ 1) (k : ℕ) : ‖w ^ k - 1‖ ≤ ‖w - 1‖ := by sorry
