-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_map
-- name    : GlobalTheory.WeilDeligne.isSemisimple_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:30.644148+00:00
-- url     : https://prove2.me/theorems/1e8f83a7-fc69-4693-8412-515cc6103141
-- title:
--   Weil Deligne: is Semisimple map
-- statement:
--   The Weil Deligne construction uses the is Semisimple map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L14-L17

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

theorem GlobalTheory.WeilDeligne.isSemisimple_map [FiniteDimensional ℂ V] (φ : End ℂ V →ₐ[ℂ] End ℂ V') {f : End ℂ V}
    (hf : f.IsSemisimple) : (φ f).IsSemisimple := by sorry
