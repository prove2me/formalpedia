-- Prove2me | Theorems.Thm_GlobalTheory_relLength_eq_add_inf_of_le
-- name    : GlobalTheory.relLength_eq_add_inf_of_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:24.462869+00:00
-- url     : https://prove2.me/theorems/8c8111b4-0e2b-4ac7-8090-42e44a9c57ee
-- title:
--   Global Theory: rel Length eq add inf of le
-- statement:
--   The Global Theory construction uses the rel Length eq add inf of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L38-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem GlobalTheory.relLength_eq_add_inf_of_le (A : Submodule R V) {B C : Submodule R V} (hCB : C ≤ B) :
    relLength A C = relLength A B + relLength (A ⊓ B) C := by sorry
