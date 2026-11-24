-- Prove2me | Theorems.Thm_GlobalTheory_span_grid_eq_span_range
-- name    : GlobalTheory.span_grid_eq_span_range
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:24.680595+00:00
-- url     : https://prove2.me/theorems/0b28e3eb-1d77-4348-bd6a-6b6361254bb2
-- title:
--   Global Theory: span grid eq span range
-- statement:
--   The Global Theory construction uses the span grid eq span range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L52-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L52-L65

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

theorem GlobalTheory.span_grid_eq_span_range (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by sorry
