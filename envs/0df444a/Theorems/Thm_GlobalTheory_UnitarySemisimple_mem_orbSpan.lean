-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySemisimple_mem_orbSpan
-- name    : GlobalTheory.UnitarySemisimple.mem_orbSpan
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:35.649213+00:00
-- url     : https://prove2.me/theorems/3f117649-2bb9-4605-8ab0-5dd5f8045e33
-- title:
--   Unitary Semisimple: mem orb Span
-- statement:
--   The Unitary Semisimple construction uses the mem orb Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIrreducibleSubrepFixedOfUnitary.lean#L108-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIrreducibleSubrepFixedOfUnitary.lean#L108-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.UnitarySemisimple.mem_orbSpan (ρ : Representation ℂ H W) (y : W) : y ∈ (orbSpan ρ y).toSubmodule := by sorry
