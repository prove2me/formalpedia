-- Prove2me | Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating_of_essFiniteType
-- name    : GlobalTheory.exists_discreteValuationSubring_dominating_of_essFiniteType
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:34.158984+00:00
-- url     : https://prove2.me/theorems/ec793ef6-4223-4c94-b2e2-cc17621e3e3a
-- title:
--   Global Theory: exists discrete Valuation Subring dominating of ess Finite Type
-- statement:
--   The Global Theory construction uses the exists discrete Valuation Subring dominating of ess Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L370-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L370-L379

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
variable {R L : Type*} [CommRing R] [IsLocalRing R] [Field L]
variable [IsNoetherianRing R] [Algebra R L]

theorem GlobalTheory.exists_discreteValuationSubring_dominating_of_essFiniteType [Algebra.EssFiniteType R L]
    [FaithfulSMul R L] (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := by sorry
