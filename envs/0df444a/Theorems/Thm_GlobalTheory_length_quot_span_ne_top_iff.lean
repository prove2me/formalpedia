-- Prove2me | Theorems.Thm_GlobalTheory_length_quot_span_ne_top_iff
-- name    : GlobalTheory.length_quot_span_ne_top_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:05:40.453875+00:00
-- url     : https://prove2.me/theorems/4ccc669b-6396-477a-94fd-8e6f24314b65
-- title:
--   Global Theory: length quot span ne top iff
-- statement:
--   The Global Theory construction uses the length quot span ne top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L236-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L236-L238

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

theorem GlobalTheory.length_quot_span_ne_top_iff (x : S) :
    Module.length R (S ⧸ Ideal.span {x}) ≠ ⊤ ↔ x ∈ nonZeroDivisors S := by sorry
