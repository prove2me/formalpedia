-- Prove2me | Theorems.Thm_GlobalTheory_length_quotient_span_singleton_eq_addVal
-- name    : GlobalTheory.length_quotient_span_singleton_eq_addVal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:05:54.885032+00:00
-- url     : https://prove2.me/theorems/3ba23cb0-e003-4e4c-90f5-36e91ed61f92
-- title:
--   Global Theory: length quotient span singleton eq add Val
-- statement:
--   The Global Theory construction uses the length quotient span singleton eq add Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L72-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L72-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open IsDiscreteValuationRing hiding maximalIdeal
variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]

theorem GlobalTheory.length_quotient_span_singleton_eq_addVal {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (x : S) :
    Module.length S (S ⧸ Ideal.span {x}) = addVal S x := by sorry
