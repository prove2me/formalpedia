-- Prove2me | Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff_isLocalHom
-- name    : GlobalTheory.localSubring_range_le_valuationSubring_iff_isLocalHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:55.516386+00:00
-- url     : https://prove2.me/theorems/b842827e-573f-4cd2-b009-ab19cf33d382
-- title:
--   Global Theory: local Subring range le valuation Subring iff is Local Hom
-- statement:
--   The Global Theory construction uses the local Subring range le valuation Subring iff is Local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L317-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L317-L329

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

theorem GlobalTheory.localSubring_range_le_valuationSubring_iff_isLocalHom (f : R →+* L)
    (V : ValuationSubring L) :
    LocalSubring.range f ≤ V.toLocalSubring ↔
      ∃ h : ∀ r, f r ∈ V, IsLocalHom (f.codRestrict V h) := by sorry
