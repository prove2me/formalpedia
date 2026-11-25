-- Prove2me | Theorems.Thm_GlobalTheory_InjectiveOfIntegral_exists_injective_of_isIntegral
-- name    : GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:21.487314+00:00
-- url     : https://prove2.me/theorems/4cab0201-9dae-4f7b-807e-0138391ef443
-- title:
--   Injective Of Integral: exists injective of is Integral
-- statement:
--   The Injective Of Integral construction uses the exists injective of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveOfIsIntegral.lean#L5-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveOfIsIntegral.lean#L5-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InjectiveOfIntegral

theorem GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal)
    (hv : Valuation.Integers v O) [Algebra A B] [Algebra.IsIntegral A B]
    (hAB : Function.Injective (algebraMap A B)) (j : A →+* O)
    (hj : Function.Injective ((algebraMap O C).comp j)) :
    ∃ j' : B →+* O, Function.Injective ((algebraMap O C).comp j') := by sorry
