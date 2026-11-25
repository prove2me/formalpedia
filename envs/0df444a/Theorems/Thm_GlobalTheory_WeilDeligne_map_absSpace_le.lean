-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_map_absSpace_le
-- name    : GlobalTheory.WeilDeligne.map_absSpace_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:20.688797+00:00
-- url     : https://prove2.me/theorems/84b7cfc5-8659-454d-ae00-5eefcd948dbe
-- title:
--   Weil Deligne: map abs Space le
-- statement:
--   The Weil Deligne construction uses the map abs Space le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L108-L114

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

theorem GlobalTheory.WeilDeligne.map_absSpace_le {f : End ℂ V} {g : End ℂ V'} (e : V →ₗ[ℂ] V') (he : ∀ v, e (f v) = g (e v))
    (r : ℝ) : (absSpace f r).map e ≤ absSpace g r := by sorry
