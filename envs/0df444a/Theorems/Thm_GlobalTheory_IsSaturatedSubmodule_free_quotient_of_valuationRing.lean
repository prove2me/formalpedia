-- Prove2me | Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_free_quotient_of_valuationRing
-- name    : GlobalTheory.IsSaturatedSubmodule.free_quotient_of_valuationRing
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:21:45.271829+00:00
-- url     : https://prove2.me/theorems/6b73a357-90f8-41dd-83c8-180632dc11bb
-- title:
--   Is Saturated Submodule: free quotient of valuation Ring
-- statement:
--   The Is Saturated Submodule construction uses the free quotient of valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L93-L96

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

theorem GlobalTheory.IsSaturatedSubmodule.free_quotient_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R (M ⧸ N) := by sorry
