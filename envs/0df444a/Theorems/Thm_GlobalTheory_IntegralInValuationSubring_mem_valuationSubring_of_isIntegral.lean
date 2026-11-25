-- Prove2me | Theorems.Thm_GlobalTheory_IntegralInValuationSubring_mem_valuationSubring_of_isIntegral
-- name    : GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:56.163407+00:00
-- url     : https://prove2.me/theorems/05e6519a-bdb0-494e-bba3-829bf47ff8d1
-- title:
--   Integral In Valuation Subring: mem valuation Subring of is Integral
-- statement:
--   The Integral In Valuation Subring construction uses the mem valuation Subring of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemValuationSubringOfIsIntegral.lean#L5-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemValuationSubringOfIsIntegral.lean#L5-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemValuationSubringOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralInValuationSubring

theorem GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral {Ω : Type} [Field Ω] {R : Type} [CommRing R]
    [Algebra R Ω] (A : ValuationSubring Ω) (h : ∀ r : R, algebraMap R Ω r ∈ A) {b : Ω}
    (hb : IsIntegral R b) : b ∈ A := by sorry
