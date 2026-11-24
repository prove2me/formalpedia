-- Prove2me | Theorems.Thm_GlobalTheory_exists_eval_ne_zero_of_countable
-- name    : GlobalTheory.exists_eval_ne_zero_of_countable
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:36.516677+00:00
-- url     : https://prove2.me/theorems/160ddabc-4551-4ed2-86e0-80307500fcbd
-- title:
--   Global Theory: exists eval ne zero of countable
-- statement:
--   The Global Theory construction uses the exists eval ne zero of countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAlgHomNeZeroOfCountable.lean#L5-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAlgHomNeZeroOfCountable.lean#L5-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomNeZeroOfCountable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_eval_ne_zero_of_countable {σ : Type} [Finite σ] (T : Set (MvPolynomial σ ℂ))
    (hT : T.Countable) (h0 : (0 : MvPolynomial σ ℂ) ∉ T) :
    ∃ c : σ → ℂ, ∀ p ∈ T, MvPolynomial.eval c p ≠ 0 := by sorry
