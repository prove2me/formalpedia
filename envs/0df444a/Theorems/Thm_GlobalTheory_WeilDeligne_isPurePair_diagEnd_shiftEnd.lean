-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_isPurePair_diagEnd_shiftEnd
-- name    : GlobalTheory.WeilDeligne.isPurePair_diagEnd_shiftEnd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:56:14.509541+00:00
-- url     : https://prove2.me/theorems/b3c071ab-4db8-406b-bd65-8f8b710217b2
-- title:
--   Weil Deligne: is Pure Pair diag End shift End
-- statement:
--   The Weil Deligne construction uses the is Pure Pair diag End shift End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L209-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L209-L258

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

theorem GlobalTheory.WeilDeligne.isPurePair_diagEnd_shiftEnd {q : ℝ} (hq : 1 < q) {n : ℕ} (c : Fin n → ℂ)
    (hc : ∀ i : Fin n, ‖c i‖ = q ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2)) :
    IsPurePair q (diagEnd c) (shiftEnd n) := by sorry
