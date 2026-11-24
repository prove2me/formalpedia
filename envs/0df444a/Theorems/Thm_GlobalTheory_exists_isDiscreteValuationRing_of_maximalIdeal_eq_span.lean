-- Prove2me | Theorems.Thm_GlobalTheory_exists_isDiscreteValuationRing_of_maximalIdeal_eq_span
-- name    : GlobalTheory.exists_isDiscreteValuationRing_of_maximalIdeal_eq_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:08.857269+00:00
-- url     : https://prove2.me/theorems/37436e57-4750-466a-b186-94b38749bdd5
-- title:
--   Global Theory: exists is Discrete Valuation Ring of maximal Ideal eq span
-- statement:
--   The Global Theory construction uses the exists is Discrete Valuation Ring of maximal Ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L323-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L323-L361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct

theorem GlobalTheory.exists_isDiscreteValuationRing_of_maximalIdeal_eq_span {B : Type*} [CommRing B]
    [IsLocalRing B] {t : B} (ht : t ∈ nonZeroDivisors B) (hm : maximalIdeal B = Ideal.span {t})
    (hs : ⨅ n : ℕ, maximalIdeal B ^ n = ⊥) :
    ∃ _ : IsDomain B, IsDiscreteValuationRing B := by sorry
