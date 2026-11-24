-- Prove2me | Theorems.Thm_GlobalTheory_lengthCommensurable_iff_sup
-- name    : GlobalTheory.lengthCommensurable_iff_sup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:06:13.355164+00:00
-- url     : https://prove2.me/theorems/14c5f7f1-5147-4544-9df3-3af79e4fa25a
-- title:
--   Global Theory: length Commensurable iff sup
-- statement:
--   The Global Theory construction uses the length Commensurable iff sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L315-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L315-L320

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

theorem GlobalTheory.lengthCommensurable_iff_sup :
    LengthCommensurable A B ↔
      LengthCommensurable (A ⊔ B) B ∧ LengthCommensurable (A ⊔ B) A := by sorry
