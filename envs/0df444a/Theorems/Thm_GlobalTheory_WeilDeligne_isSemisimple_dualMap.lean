-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_dualMap
-- name    : GlobalTheory.WeilDeligne.isSemisimple_dualMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:55:44.822848+00:00
-- url     : https://prove2.me/theorems/63aeb0eb-f65f-43ae-99cb-5e75910e1586
-- title:
--   Weil Deligne: is Semisimple dual Map
-- statement:
--   The Weil Deligne construction uses the is Semisimple dual Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L74-L77

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

theorem GlobalTheory.WeilDeligne.isSemisimple_dualMap [FiniteDimensional ℂ V] {f : End ℂ V} (hf : f.IsSemisimple) :
    End.IsSemisimple (f.dualMap : End ℂ (Dual ℂ V)) := by sorry
