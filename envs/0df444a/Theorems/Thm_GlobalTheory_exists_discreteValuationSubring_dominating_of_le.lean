-- Prove2me | Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating_of_le
-- name    : GlobalTheory.exists_discreteValuationSubring_dominating_of_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:40.192221+00:00
-- url     : https://prove2.me/theorems/d014d244-0ebb-4cb5-8c10-1caacb1a657e
-- title:
--   Global Theory: exists discrete Valuation Subring dominating of le
-- statement:
--   The Global Theory construction uses the exists discrete Valuation Subring dominating of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L333-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L333-L368

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

theorem GlobalTheory.exists_discreteValuationSubring_dominating_of_le [Algebra.EssFiniteType R L]
    (W : ValuationSubring L) (hW : LocalSubring.range (algebraMap R L) ≤ W.toLocalSubring)
    {s t : Set L} (hsf : s.Finite) (htf : t.Finite) (hs : ∀ x ∈ s, x ∈ W)
    (ht : ∀ x ∈ t, x ∈ W.nonunits)
    (h0 : (∃ r ∈ maximalIdeal R, algebraMap R L r ≠ 0) ∨ ∃ x ∈ t, x ≠ 0) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring ∧
      (∀ x ∈ s, x ∈ V) ∧ ∀ x ∈ t, x ∈ V.nonunits := by sorry
