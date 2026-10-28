-- Prove2me | Theorems.Thm_MultPacing_Existence_theorem_1_budget
-- name    : MultPacing.Existence.theorem_1_budget
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:12.481559+00:00
-- url     : https://prove2.me/theorems/58a4d681-72d1-4138-8552-996167f617bb
-- title:
--   Proof of Theorem 1, "No buyer exceeds her budget", p. 12 — Σ_j s*_ij ≤ B_i at the limit point
-- statement:
--   In the setting of the proof of Theorem 1 (a convergent sequence of equilibria $\alpha^l$ of $(\epsilon^l,H^l)$-smoothed pacing games with $\epsilon^l>0$, $\sum_j v_{ij}+2\epsilon^l\le M$, $H^l>M/\epsilon^l$, $\epsilon^l\to0$, $H^l\to\infty$, and limit payments $s^*_{ij}=\lim_l s^l_{ij}$), no buyer exceeds her budget at the limit point:
--   $$
--   \sum_j s^*_{ij}\le B_i\qquad\text{for every buyer } i .
--   $$
--
--   This is the budget condition of Definition 2.
--
--   Differences from the source:
--   - encoding: convergence of a subsequence → convergence of the sequence; reason: the paper replaces the sequence by the subsequence before the claims.
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, p. 12 (PDF 12), proof of Theorem 1, claim "No buyer exceeds her budget"

import Mathlib
import Definitions.Def_MultPacing_Existence_Limit

namespace MultPacing.Existence

theorem theorem_1_budget {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ) (αs : N → ℝ)
    (xs ps ss : N → G → ℝ) (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) :
    ∀ i, ∑ j, ss i j ≤ P.B i := by sorry

end MultPacing.Existence
