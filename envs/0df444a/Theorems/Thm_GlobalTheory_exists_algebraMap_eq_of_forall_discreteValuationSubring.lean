-- Prove2me | Theorems.Thm_GlobalTheory_exists_algebraMap_eq_of_forall_discreteValuationSubring
-- name    : GlobalTheory.exists_algebraMap_eq_of_forall_discreteValuationSubring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:39.007413+00:00
-- url     : https://prove2.me/theorems/06d03518-ecc4-4a55-ad05-23fd3092a330
-- title:
--   Global Theory: exists algebra Map eq of forall discrete Valuation Subring
-- statement:
--   The Global Theory construction uses the exists algebra Map eq of forall discrete Valuation Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L588-L596
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L588-L596

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
variable {R K}

theorem GlobalTheory.exists_algebraMap_eq_of_forall_discreteValuationSubring [IsIntegrallyClosed R] {x : K}
    (hx : ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ r, algebraMap R K r ∈ V) →
      (∀ r ∈ maximalIdeal R, algebraMap R K r ∈ V.nonunits) → x ∈ V) :
    ∃ r : R, algebraMap R K r = x := by sorry
