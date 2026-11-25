-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_diagEnd
-- name    : GlobalTheory.WeilDeligne.isSemisimple_diagEnd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:56:28.551907+00:00
-- url     : https://prove2.me/theorems/3b33bc83-59e3-4255-85c6-7e62f8d00370
-- title:
--   Weil Deligne: is Semisimple diag End
-- statement:
--   The Weil Deligne construction uses the is Semisimple diag End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L86-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L86-L96

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

theorem GlobalTheory.WeilDeligne.isSemisimple_diagEnd {ι : Type*} [Finite ι] (c : ι → ℂ) : (diagEnd c).IsSemisimple := by sorry
