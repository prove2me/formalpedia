-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_of_iSup_eigenspace
-- name    : GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:10.760332+00:00
-- url     : https://prove2.me/theorems/5a1d27f1-0abb-52c4-bc2c-ae5e4d3ec741
-- title:
--   Weil Deligne: is Semisimple of i Sup eigenspace
-- statement:
--   The Weil Deligne construction uses the is Semisimple of i Sup eigenspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L19-L35

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

theorem GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace [FiniteDimensional ℂ V] {f : End ℂ V}
    (hf : ⨆ α, f.eigenspace α = ⊤) : f.IsSemisimple := by sorry
