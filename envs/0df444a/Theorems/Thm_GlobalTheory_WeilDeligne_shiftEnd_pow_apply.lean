-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_shiftEnd_pow_apply
-- name    : GlobalTheory.WeilDeligne.shiftEnd_pow_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:03.332046+00:00
-- url     : https://prove2.me/theorems/8b96699e-c05c-57d7-ab60-bf010b734c08
-- title:
--   Weil Deligne: shift End pow apply
-- statement:
--   The Weil Deligne construction uses the shift End pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L185-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L185-L198

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

theorem GlobalTheory.WeilDeligne.shiftEnd_pow_apply {n : ℕ} (k : ℕ) (v : Fin n → ℂ) (i : Fin n) :
    (shiftEnd n ^ k) v i = if k ≤ (i : ℕ) then v ⟨i - k, by omega⟩ else 0 := by sorry
