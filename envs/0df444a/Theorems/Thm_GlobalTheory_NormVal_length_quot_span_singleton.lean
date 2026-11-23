-- Prove2me | Theorems.Thm_GlobalTheory_NormVal_length_quot_span_singleton
-- name    : GlobalTheory.NormVal.length_quot_span_singleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:36.277195+00:00
-- url     : https://prove2.me/theorems/cf1dcc74-7114-4f84-b264-19980df02c02
-- title:
--   Norm Val: length quot span singleton
-- statement:
--   The Norm Val construction uses the length quot span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L14-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

theorem GlobalTheory.NormVal.length_quot_span_singleton (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a := by sorry
