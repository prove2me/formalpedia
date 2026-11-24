-- Prove2me | Theorems.Thm_GlobalTheory_eval_rowOps_eq
-- name    : GlobalTheory.eval_rowOps_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:48.534826+00:00
-- url     : https://prove2.me/theorems/6be09ad1-ad00-4d2d-87af-926522cd657e
-- title:
--   Global Theory: eval row Ops eq
-- statement:
--   The Global Theory construction uses the eval row Ops eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ColumnDegreeLe.lean#L7-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ColumnDegreeLe.lean#L7-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ColumnDegreeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory

theorem GlobalTheory.eval_rowOps_eq {K σ : Type*} [Field K] [DecidableEq σ] {p n : ℕ} (z : Fin p × Fin n → σ)
    (hz : Function.Injective z) (P : MvPolynomial σ K)
    (hinv : ∀ a b : Fin p, a < b → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (i : ℕ) (c : Fin p × Fin p → K) (x : σ → K) (T : Finset (Fin p × Fin p))
    (hT : ∀ q ∈ T, (q.1 : ℕ) < i ∧ i ≤ (q.2 : ℕ)) :
    eval (fun s => x s + ∑ q ∈ T, ∑ k, if s = z (q.2, k) then c q * x (z (q.1, k)) else 0) P
      = eval x P := by sorry
