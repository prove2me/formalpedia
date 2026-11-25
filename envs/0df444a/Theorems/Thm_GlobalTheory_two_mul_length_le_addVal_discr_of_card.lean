-- Prove2me | Theorems.Thm_GlobalTheory_two_mul_length_le_addVal_discr_of_card
-- name    : GlobalTheory.two_mul_length_le_addVal_discr_of_card
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:13.249865+00:00
-- url     : https://prove2.me/theorems/71f13330-12fb-5c5a-86db-e3335601efd0
-- title:
--   Global Theory: two mul length le add Val discr of card
-- statement:
--   The Global Theory construction uses the two mul length le add Val discr of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L44-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]
variable [IsDomain R] [IsDiscreteValuationRing R]

theorem GlobalTheory.two_mul_length_le_addVal_discr_of_card [Module.Free R S] [Module.Finite R S]
    (h : Fintype.card ι = finrank R S) (v : ι → S) :
    2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) ≤ addVal R (Algebra.discr R v) := by sorry
