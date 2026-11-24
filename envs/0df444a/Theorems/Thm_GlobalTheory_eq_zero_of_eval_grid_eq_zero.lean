-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_eval_grid_eq_zero
-- name    : GlobalTheory.eq_zero_of_eval_grid_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:18:01.454813+00:00
-- url     : https://prove2.me/theorems/c941c712-e78a-468a-8e24-3347a4245fe2
-- title:
--   Global Theory: eq zero of eval grid eq zero
-- statement:
--   The Global Theory construction uses the eq zero of eval grid eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L24-L27

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

theorem GlobalTheory.eq_zero_of_eval_grid_eq_zero (d : ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → eval (fun i => (x i : R)) P = 0) : P = 0 := by sorry
