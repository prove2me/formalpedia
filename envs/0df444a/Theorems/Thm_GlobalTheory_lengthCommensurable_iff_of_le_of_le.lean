-- Prove2me | Theorems.Thm_GlobalTheory_lengthCommensurable_iff_of_le_of_le
-- name    : GlobalTheory.lengthCommensurable_iff_of_le_of_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:54.400088+00:00
-- url     : https://prove2.me/theorems/94ea51f1-dfc8-4262-bf12-fadd1fd15c92
-- title:
--   Global Theory: length Commensurable iff of le of le
-- statement:
--   The Global Theory construction uses the length Commensurable iff of le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L96-L100

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
variable {A A' B B' C : Submodule R V}

theorem GlobalTheory.lengthCommensurable_iff_of_le_of_le (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A C ↔ LengthCommensurable A B ∧ LengthCommensurable B C := by sorry
