-- Prove2me | Theorems.Thm_GlobalTheory_UltrametricPowerBound_ultra
-- name    : GlobalTheory.UltrametricPowerBound.ultra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:50.079834+00:00
-- url     : https://prove2.me/theorems/6b39bc6a-6e35-470c-a9e7-e59c3a1defa1
-- title:
--   Ultrametric Power Bound: ultra
-- statement:
--   The Ultrametric Power Bound construction uses the ultra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubOneLe.lean#L7-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubOneLe.lean#L7-L7

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

theorem GlobalTheory.UltrametricPowerBound.ultra (q r : ℚ_[l]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := by sorry
