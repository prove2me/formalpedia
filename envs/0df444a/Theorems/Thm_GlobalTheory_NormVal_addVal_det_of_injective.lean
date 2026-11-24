-- Prove2me | Theorems.Thm_GlobalTheory_NormVal_addVal_det_of_injective
-- name    : GlobalTheory.NormVal.addVal_det_of_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:40.216785+00:00
-- url     : https://prove2.me/theorems/913d4fad-3fad-4f22-8e2c-c4fc99546e4c
-- title:
--   Norm Val: add Val det of injective
-- statement:
--   The Norm Val construction uses the add Val det of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L24-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L24-L54

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

theorem GlobalTheory.NormVal.addVal_det_of_injective (f : M →ₗ[R] M) (hf : Function.Injective f) :
    addVal R (LinearMap.det f) = Module.length R (M ⧸ LinearMap.range f) := by sorry
