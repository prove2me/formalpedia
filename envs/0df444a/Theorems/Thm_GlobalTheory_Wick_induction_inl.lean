-- Prove2me | Theorems.Thm_GlobalTheory_Wick_induction_inl
-- name    : GlobalTheory.Wick.induction_inl
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:34.2776+00:00
-- url     : https://prove2.me/theorems/d96dadfc-c0f8-4bbf-8454-455ce524ce9e
-- title:
--   Wick: induction inl
-- statement:
--   The Wick construction uses the induction inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L224-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L224-L230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Wick
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}

theorem GlobalTheory.Wick.induction_inl {p : MvPolynomial (ι ⊕ κ) R → Prop}
    (h0 : ∀ q : MvPolynomial κ R, p (rename Sum.inr q))
    (hadd : ∀ P Q, p P → p Q → p (P + Q))
    (h : ∀ P (i : ι), p P → p (X (Sum.inl i) * P)) (P : MvPolynomial (ι ⊕ κ) R) : p P := by sorry
