-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_mem_absSpace_diagEnd
-- name    : GlobalTheory.WeilDeligne.mem_absSpace_diagEnd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:37.692238+00:00
-- url     : https://prove2.me/theorems/5c1ce149-7956-413b-a36f-b40932f2774f
-- title:
--   Weil Deligne: mem abs Space diag End
-- statement:
--   The Weil Deligne construction uses the mem abs Space diag End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L152-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L152-L175

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

theorem GlobalTheory.WeilDeligne.mem_absSpace_diagEnd {ι : Type*} [Finite ι] (c : ι → ℂ) (r : ℝ) (v : ι → ℂ) :
    v ∈ absSpace (diagEnd c) r ↔ ∀ i, ‖c i‖ ≠ r → v i = 0 := by sorry
