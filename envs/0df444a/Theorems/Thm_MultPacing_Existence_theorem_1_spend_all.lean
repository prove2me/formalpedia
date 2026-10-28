-- Prove2me | Theorems.Thm_MultPacing_Existence_theorem_1_spend_all
-- name    : MultPacing.Existence.theorem_1_spend_all
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:52.621994+00:00
-- url     : https://prove2.me/theorems/3ccb5c79-90cd-4cc4-a672-3e2196cb388a
-- title:
--   Proof of Theorem 1, "A buyer with α*_i < 1 spends her entire budget", p. 12 — α*_i < 1 implies Σ_j s*_ij = B_i
-- statement:
--   In the setting of the proof of Theorem 1 (a convergent sequence of equilibria $\alpha^l$ of $(\epsilon^l,H^l)$-smoothed pacing games with $\epsilon^l>0$, $\sum_j v_{ij}+2\epsilon^l\le M$, $H^l>M/\epsilon^l$, $\epsilon^l\to0$, $H^l\to\infty$, limit multipliers $\alpha^*$ and limit payments $s^*$), a buyer who is paced at the limit spends her entire budget:
--   $$
--   \alpha^*_i<1\ \Longrightarrow\ \sum_j s^*_{ij}=B_i .
--   $$
--
--   Together with the budget claim this gives the no-unnecessary-pacing condition of Definition 2.
--
--   Differences from the source:
--   - encoding: convergence of a subsequence → convergence of the sequence; reason: the paper replaces the sequence by the subsequence before the claims.
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, p. 12 (PDF 12), proof of Theorem 1, claim "A buyer with α*_i < 1 spends her entire budget"

import Mathlib
import Definitions.Def_MultPacing_Existence_Limit

namespace MultPacing.Existence

theorem theorem_1_spend_all {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ) (αs : N → ℝ)
    (xs ps ss : N → G → ℝ) (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) :
    ∀ i, αs i < 1 → ∑ j, ss i j = P.B i := by sorry

end MultPacing.Existence
