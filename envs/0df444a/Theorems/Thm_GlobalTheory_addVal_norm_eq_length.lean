-- Prove2me | Theorems.Thm_GlobalTheory_addVal_norm_eq_length
-- name    : GlobalTheory.addVal_norm_eq_length
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:01.464344+00:00
-- url     : https://prove2.me/theorems/59e9f85b-4886-4ba2-891d-3147d0dd7fb2
-- title:
--   Global Theory: add Val norm eq length
-- statement:
--   The Global Theory construction uses the add Val norm eq length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L221-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L221-L228

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
open NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]

theorem GlobalTheory.addVal_norm_eq_length (x : S) :
    addVal R (Algebra.norm R x) = Module.length R (S ⧸ Ideal.span {x}) := by sorry
