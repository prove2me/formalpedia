-- Prove2me | Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_free_of_valuationRing
-- name    : GlobalTheory.IsSaturatedSubmodule.free_of_valuationRing
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:48.932249+00:00
-- url     : https://prove2.me/theorems/cb674c56-a379-406d-b012-7b59ff62c0e1
-- title:
--   Is Saturated Submodule: free of valuation Ring
-- statement:
--   The Is Saturated Submodule construction uses the free of valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L108-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSaturatedSubmoduleIffExistsIsComplOfValuationR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

theorem GlobalTheory.IsSaturatedSubmodule.free_of_valuationRing [Module.Finite R M] [Module.IsTorsionFree R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R N := by sorry
