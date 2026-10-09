-- Prove2me | Theorems.Thm_GhadimiLan_TwoPhase_eq_2_28
-- name    : GhadimiLan.TwoPhase.eq_2_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:39.030864+00:00
-- url     : https://prove2.me/theorems/328811e0-724b-4bd3-8952-e3f15fc10106
-- title:
--   Equation (2.28) — selected-gradient deterministic inequality
-- statement:
--   Let $a_s$ be the true gradients at $S\ge1$ candidates, and $b_s$ their estimated gradients. Choose any $s^*$ minimizing $\|b_s\|$. Then
--
--   $$\|a_{s^*}\|^2\le4\min_s\|a_s\|^2+4\max_s\|b_s-a_s\|^2+2\|a_{s^*}-b_{s^*}\|^2.$$
--
--   This deterministic relation connects the selected candidate to the best true gradient and to estimation errors.
--
--   **Formalization Note** The finite minimum and maximum are taken over the nonempty candidate set `Fin S`; the vectors abstract the paper's $\nabla f(\bar x_s)$ and $\widehat g_s$.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Eq. (2.28), proof of Theorem 2.4(a), p. 12

import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Equation (2.28), p. 12, abstracted from candidate gradients and estimates. -/
theorem eq_2_28 {n S : ℕ} (hS : 0 < S)
    (a b : Fin S → GhadimiLan.RSG.E n) (sStar : Fin S)
    (hmin : ∀ s, ‖b sStar‖ ≤ ‖b s‖) :
    ‖a sStar‖ ^ 2 ≤
      4 * (Finset.univ : Finset (Fin S)).inf'
        (by exact ⟨⟨0, hS⟩, Finset.mem_univ _⟩) (fun s => ‖a s‖ ^ 2) +
      4 * (Finset.univ : Finset (Fin S)).sup'
        (by exact ⟨⟨0, hS⟩, Finset.mem_univ _⟩) (fun s => ‖b s - a s‖ ^ 2) +
      2 * ‖a sStar - b sStar‖ ^ 2 := by sorry

end GhadimiLan.TwoPhase
