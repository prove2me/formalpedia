-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_eval_box_eq_zero
-- name    : GlobalTheory.eq_zero_of_eval_box_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:52.421438+00:00
-- url     : https://prove2.me/theorems/42e4ff34-7966-417d-acee-6e79ab29d199
-- title:
--   Global Theory: eq zero of eval box eq zero
-- statement:
--   The Global Theory construction uses the eq zero of eval box eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L11-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R] [CharZero R]

theorem GlobalTheory.eq_zero_of_eval_box_eq_zero (d : σ → ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d i)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d i) → eval (fun i => (x i : R)) P = 0) : P = 0 := by sorry
