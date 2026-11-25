-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_shiftEnd_apply
-- name    : GlobalTheory.WeilDeligne.shiftEnd_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:07.471984+00:00
-- url     : https://prove2.me/theorems/c05aeaca-0fc1-59d3-88f1-645a6460967d
-- title:
--   Weil Deligne: shift End apply
-- statement:
--   The Weil Deligne construction uses the shift End apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L182-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L182-L183

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

theorem GlobalTheory.WeilDeligne.shiftEnd_apply {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    shiftEnd n v i = if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0 := by sorry
