-- Prove2me | Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_addVal_prod
-- name    : GlobalTheory.LengthQuotientSpanValuation.addVal_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:33.856531+00:00
-- url     : https://prove2.me/theorems/fa35c542-05d7-40bf-b5a3-4d89b59d553e
-- title:
--   Length Quotient Span Valuation: add Val prod
-- statement:
--   The Length Quotient Span Valuation construction uses the add Val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthSelfEqTop.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthSelfEqTop.lean#L20-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthSelfEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.LengthQuotientSpanValuation
open Module
variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem GlobalTheory.LengthQuotientSpanValuation.addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (a i) := by sorry
