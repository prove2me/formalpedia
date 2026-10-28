-- Prove2me | Theorems.Thm_MultPacing_Existence_theorem_1_feasible
-- name    : MultPacing.Existence.theorem_1_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:03.356072+00:00
-- url     : https://prove2.me/theorems/04d063c4-8195-416b-9aa5-87d5c2134b41
-- title:
--   Proof of Theorem 1, "The allocation is feasible", p. 12 — the limit allocation is feasible, full when valued, and goes to highest bidders
-- statement:
--   Fix a pacing game $(v,B)$ and a convergent sequence of smoothed equilibria as in the proof of Theorem 1: $\epsilon^l>0$, $\sum_j v_{ij}+2\epsilon^l\le M$, $H^l>M/\epsilon^l$, $\epsilon^l\to0$, $H^l\to\infty$, $\alpha^l$ a pure-strategy Nash equilibrium of the $(\epsilon^l,H^l)$-smoothed game, and $\alpha^l\to\alpha^*$, $x^l_{ij}\to x^*_{ij}$, $p^l_{ij}\to p^*_{ij}$, $s^l_{ij}\to s^*_{ij}$. Then the limit allocation is feasible:
--
--   1. $\sum_i x^*_{ij}\le1$ for every good $j$;
--   2. $\sum_i x^*_{ij}=1$ for every good $j$ such that some buyer $i$ has $v_{ij}>0$;
--   3. if $x^*_{ij}>0$ then $i$ is at least tied for the highest limit bid on $j$:
--   $$
--   x^*_{ij}>0\ \Longrightarrow\ \alpha^*_k v_{kj}\le\alpha^*_i v_{ij}\quad\text{for every buyer }k .
--   $$
--
--   These are the allocation conditions of Definition 2 at the limit point.
--
--   **Formalization Note** The sequence and its limits are bundled in `IsSmoothedLimit`; the sequence is assumed convergent, which is the paper's passage to a convergent subsequence.
--
--   Differences from the source:
--   - encoding: "this sequence must have a subsequence with a limit point … replace the sequence by this subsequence" → the sequence itself is assumed to converge; reason: the claims are stated after that replacement.
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, p. 12 (PDF 12), proof of Theorem 1, claim "The allocation is feasible"

import Mathlib
import Definitions.Def_MultPacing_Existence_Limit

namespace MultPacing.Existence

theorem theorem_1_feasible {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ) (αs : N → ℝ)
    (xs ps ss : N → G → ℝ) (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) :
    (∀ j, ∑ i, xs i j ≤ 1) ∧
    (∀ j, (∃ i, 0 < P.v i j) → ∑ i, xs i j = 1) ∧
    (∀ i j, 0 < xs i j → ∀ k, αs k * P.v k j ≤ αs i * P.v i j) := by sorry

end MultPacing.Existence
