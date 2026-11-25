-- Prove2me | Theorems.Thm_GlobalTheory_lengthCommensurable_iff_isFiniteLength
-- name    : GlobalTheory.lengthCommensurable_iff_isFiniteLength
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:48:13.079703+00:00
-- url     : https://prove2.me/theorems/983ea4d5-a9b5-5e07-8ce8-7f310aa7397a
-- title:
--   Global Theory: length Commensurable iff is Finite Length
-- statement:
--   The Global Theory construction uses the length Commensurable iff is Finite Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L279-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L279-L282

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {A B : Submodule R V}

theorem GlobalTheory.lengthCommensurable_iff_isFiniteLength :
    LengthCommensurable A B ↔
      IsFiniteLength R (A ⧸ B.submoduleOf A) ∧ IsFiniteLength R (B ⧸ A.submoduleOf B) := by sorry
