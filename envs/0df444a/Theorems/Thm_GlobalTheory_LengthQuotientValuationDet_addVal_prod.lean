-- Prove2me | Theorems.Thm_GlobalTheory_LengthQuotientValuationDet_addVal_prod
-- name    : GlobalTheory.LengthQuotientValuationDet.addVal_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:28.791085+00:00
-- url     : https://prove2.me/theorems/30742af2-76bc-4fbd-8077-c53a82a5b715
-- title:
--   Length Quotient Valuation Det: add Val prod
-- statement:
--   The Length Quotient Valuation Det construction uses the add Val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientSpanSingleton.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientSpanSingleton.lean#L11-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthQuotientValuationDet
open Module IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem GlobalTheory.LengthQuotientValuationDet.addVal_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) := by sorry
