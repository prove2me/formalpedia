-- Prove2me | Theorems.Thm_GlobalTheory_IsSaturatedIn_finite_of_valuationRing
-- name    : GlobalTheory.IsSaturatedIn.finite_of_valuationRing
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:06.980685+00:00
-- url     : https://prove2.me/theorems/537c9e92-3cb7-532e-9f47-8381bfaaa358
-- title:
--   Is Saturated In: finite of valuation Ring
-- statement:
--   The Is Saturated In construction uses the finite of valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L113-L116

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

theorem GlobalTheory.IsSaturatedIn.finite_of_valuationRing {P N : Submodule R M} [Module.Finite R P]
    (h : IsSaturatedIn P N) : Module.Finite R N := by sorry
