-- Prove2me | Theorems.Thm_GlobalTheory_span_grid_eval_eq_span_range
-- name    : GlobalTheory.span_grid_eval_eq_span_range
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:51:07.097672+00:00
-- url     : https://prove2.me/theorems/e7751722-a482-44ad-9b91-58a988723f3e
-- title:
--   Global Theory: span grid eval eq span range
-- statement:
--   The Global Theory construction uses the span grid eval eq span range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L93-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L93-L106

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
variable {σ A K V : Type*} [Finite σ] [Field K] [CharZero K] [CommSemiring A] [Algebra A K]
  [AddCommGroup V] [Module K V]

theorem GlobalTheory.span_grid_eval_eq_span_range {B : Type*} [CommRing B] [Algebra K B] (d : ℕ)
    (F : MvPolynomial σ B) (hF : ∀ i, F.degreeOf i ≤ d) :
    Submodule.span K ((fun x : σ → ℕ => eval (fun i => (x i : B)) F) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range fun x : σ → A =>
        eval (fun i => algebraMap K B (algebraMap A K (x i))) F) := by sorry
