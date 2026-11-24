-- Prove2me | Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_of_valuationSubring
-- name    : GlobalTheory.exists_discreteValuationSubring_of_valuationSubring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:27:22.724432+00:00
-- url     : https://prove2.me/theorems/1894b0f8-04d8-49a9-9596-815b90ccadb6
-- title:
--   Global Theory: exists discrete Valuation Subring of valuation Subring
-- statement:
--   The Global Theory construction uses the exists discrete Valuation Subring of valuation Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L224-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L224-L293

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
variable {L : Type*} [Field L]
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [Algebra R L]

theorem GlobalTheory.exists_discreteValuationSubring_of_valuationSubring [Algebra.EssFiniteType R L]
    (W : ValuationSubring L) (hW : ∀ r, algebraMap R L r ∈ W) {s t : Set L} (hsf : s.Finite)
    (htf : t.Finite) (hs : ∀ x ∈ s, x ∈ W) (ht : ∀ x ∈ t, x ∈ W.nonunits) (h0 : ∃ x ∈ t, x ≠ 0) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ (∀ r, algebraMap R L r ∈ V) ∧
      (∀ x ∈ s, x ∈ V) ∧ ∀ x ∈ t, x ∈ V.nonunits := by sorry
