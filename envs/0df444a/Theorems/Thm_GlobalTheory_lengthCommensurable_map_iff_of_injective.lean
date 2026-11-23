-- Prove2me | Theorems.Thm_GlobalTheory_lengthCommensurable_map_iff_of_injective
-- name    : GlobalTheory.lengthCommensurable_map_iff_of_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:58.787752+00:00
-- url     : https://prove2.me/theorems/8a7f204d-1507-4b38-a1c5-b72ad682d6b5
-- title:
--   Global Theory: length Commensurable map iff of injective
-- statement:
--   The Global Theory construction uses the length Commensurable map iff of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L192-L195

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
variable {R S V V' : Type*} [Ring R] [Ring S] [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module S V'] {σ : R →+* S} [RingHomSurjective σ]

theorem GlobalTheory.lengthCommensurable_map_iff_of_injective (f : V →ₛₗ[σ] V') (hf : Function.Injective f)
    {A B : Submodule R V} :
    LengthCommensurable (A.map f) (B.map f) ↔ LengthCommensurable A B := by sorry
