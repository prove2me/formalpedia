-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_shiftEnd_ne_zero
-- name    : GlobalTheory.WeilDeligne.shiftEnd_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:46.152805+00:00
-- url     : https://prove2.me/theorems/99222865-e5ff-431a-b6d9-cc351a406adf
-- title:
--   Weil Deligne: shift End ne zero
-- statement:
--   The Weil Deligne construction uses the shift End ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L204-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L204-L207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem GlobalTheory.WeilDeligne.shiftEnd_ne_zero {n : ℕ} (hn : 2 ≤ n) : shiftEnd n ≠ 0 := by sorry
