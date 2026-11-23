-- Prove2me | Theorems.Thm_GlobalTheory_free_of_finite_of_isTorsionFree_of_valuationRing
-- name    : GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:22.261072+00:00
-- url     : https://prove2.me/theorems/462a097c-e80b-43dc-9be3-e303fe0771fd
-- title:
--   Global Theory: free of finite of is Torsion Free of valuation Ring
-- statement:
--   The Global Theory construction uses the free of finite of is Torsion Free of valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L87-L91

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
variable (R M)

theorem GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Free R M := by sorry
