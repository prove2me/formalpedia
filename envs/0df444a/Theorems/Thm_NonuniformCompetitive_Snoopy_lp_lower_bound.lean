-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_lp_lower_bound
-- name    : NonuniformCompetitive.Snoopy.lp_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:48:06.280112+00:00
-- url     : https://prove2.me/theorems/a4c37f73-3559-45fb-821d-6c387fdd659d
-- title:
--   §3.2, pp. 552–553 — the phase LP for snoopy caching has minimum $e_p/(e_p-1)$
-- statement:
--   Let $p \ge 1$ be an integer. Let $\pi_1, \dots, \pi_{p+1}$ be real numbers with $\pi_{p+1} = 1$, and let $\alpha$ be a real number such that for every $k = 0, 1, \dots, p$,
--
--   $$\pi_{k+1}\, p + \sum_{i=1}^{k} (1 - \pi_i) \le \alpha \cdot k.$$
--
--   Then
--
--   $$\alpha \ge \frac{e_p}{e_p - 1}, \qquad e_p = \left(1 + \frac1p\right)^p .$$
--
--   In the paper, $\pi_k$ is the probability that a phase-based algorithm has made the block private to the active processor before the $k$-th write of a phase, the left-hand side is its expected cost on a phase with $k$ writes, and $k$ is the optimal cost of such a phase. The result is the LP lower bound of the proof of Theorem 4: no phase-based algorithm has an LP bound below $e_p/(e_p-1)$.
--
--   **Formalization Note** As in the paper, the $\pi_k$ are free real variables: no constraint $0 \le \pi_k \le 1$ is imposed, which makes the statement stronger. The sequence is a function $\mathbb{N} \to \mathbb{R}$; its values at $0$ and above $p+1$ are unused.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), pp. 552–553, §3.2 (proof of Theorem 4), displays for E C_A(σ_k), E C_A(σ_k) ≤ α·k and α = e_p/(e_p − 1)

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_ep

namespace NonuniformCompetitive.Snoopy

/-- The phase LP of Karlin–Manasse–McGeoch–Owicki (Algorithmica 11 (1994), §3.2, pp. 552–553)
has minimum `e_p / (e_p − 1)`. For a block-transfer cost `p ≥ 1`, let `π₁, …, π_{p+1}` be real
numbers (free variables: no sign or box constraints) with `π_{p+1} = 1`, and let `α` be a real
number such that for every `k = 0, …, p`,
`π_{k+1} · p + ∑_{i=1}^{k} (1 − π_i) ≤ α · k`.
Then `α ≥ e_p / (e_p − 1)`. The values `π 0` and `π k` for `k > p + 1` are unused. -/
theorem lp_lower_bound (p : ℕ) (hp : 1 ≤ p) (π : ℕ → ℝ) (α : ℝ)
    (hπ : π (p + 1) = 1)
    (hcon : ∀ k ≤ p, π (k + 1) * p + ∑ i ∈ Finset.Icc 1 k, (1 - π i) ≤ α * k) :
    ep p / (ep p - 1) ≤ α := by sorry

end NonuniformCompetitive.Snoopy
