-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_mem_absSpace_iff
-- name    : GlobalTheory.WeilDeligne.mem_absSpace_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:55:18.112327+00:00
-- url     : https://prove2.me/theorems/138e2a1d-227d-562d-aa31-4c8633041e6b
-- title:
--   Weil Deligne: mem abs Space iff
-- statement:
--   The Weil Deligne construction uses the mem abs Space iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L116-L121

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

theorem GlobalTheory.WeilDeligne.mem_absSpace_iff {f : End ℂ V} {g : End ℂ V'} (e : V ≃ₗ[ℂ] V')
    (he : ∀ v, e (f v) = g (e v)) (r : ℝ) (v : V) : e v ∈ absSpace g r ↔ v ∈ absSpace f r := by sorry
