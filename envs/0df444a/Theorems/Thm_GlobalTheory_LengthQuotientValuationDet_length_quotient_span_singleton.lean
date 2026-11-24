-- Prove2me | Theorems.Thm_GlobalTheory_LengthQuotientValuationDet_length_quotient_span_singleton
-- name    : GlobalTheory.LengthQuotientValuationDet.length_quotient_span_singleton
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:01:21.700781+00:00
-- url     : https://prove2.me/theorems/3c84190e-f3e1-4f56-bcf2-3f502e811769
-- title:
--   Length Quotient Valuation Det: length quotient span singleton
-- statement:
--   The Length Quotient Valuation Det construction uses the length quotient span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientSpanSingleton.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientSpanSingleton.lean#L18-L23

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

theorem GlobalTheory.LengthQuotientValuationDet.length_quotient_span_singleton {x : R} (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({x} : Set R)) = addVal R x := by sorry
