-- Prove2me | Theorems.Thm_GlobalTheory_addVal_norm_ne_top_iff
-- name    : GlobalTheory.addVal_norm_ne_top_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:53.791909+00:00
-- url     : https://prove2.me/theorems/8cebca9a-a675-4649-b13c-6c954a91e74a
-- title:
--   Global Theory: add Val norm ne top iff
-- statement:
--   The Global Theory construction uses the add Val norm ne top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L230-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L230-L234

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

theorem GlobalTheory.addVal_norm_ne_top_iff (x : S) :
    addVal R (Algebra.norm R x) ≠ ⊤ ↔ x ∈ nonZeroDivisors S := by sorry
