-- Prove2me | Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff
-- name    : GlobalTheory.localSubring_range_le_valuationSubring_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:53.011192+00:00
-- url     : https://prove2.me/theorems/795fb557-a04c-455b-ab8f-163b1f5cf230
-- title:
--   Global Theory: local Subring range le valuation Subring iff
-- statement:
--   The Global Theory construction uses the local Subring range le valuation Subring iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L301-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L301-L315

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

theorem GlobalTheory.localSubring_range_le_valuationSubring_iff (f : R →+* L) (V : ValuationSubring L) :
    LocalSubring.range f ≤ V.toLocalSubring ↔
      (∀ r, f r ∈ V) ∧ ∀ r ∈ maximalIdeal R, f r ∈ V.nonunits := by sorry
