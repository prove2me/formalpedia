-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_charpoly_diagEnd
-- name    : GlobalTheory.WeilDeligne.charpoly_diagEnd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:14.413826+00:00
-- url     : https://prove2.me/theorems/8b99af0c-a23c-5bba-8896-79ddbadb5a95
-- title:
--   Weil Deligne: charpoly diag End
-- statement:
--   The Weil Deligne construction uses the charpoly diag End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L98-L104

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

theorem GlobalTheory.WeilDeligne.charpoly_diagEnd {ι : Type*} [Fintype ι] (c : ι → ℂ) :
    (diagEnd c).charpoly = ∏ i, (X - C (c i)) := by sorry
