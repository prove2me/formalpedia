-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_lp_attained
-- name    : NonuniformCompetitive.Snoopy.lp_attained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:48:39.790188+00:00
-- url     : https://prove2.me/theorems/dccd190c-2189-4476-83f1-a03857815d8c
-- title:
--   §3.2, pp. 553–554 — the minimiser $\pi_k=(\alpha-1)(((p+1)/p)^{k-1}-1)$ is a valid algorithm
-- statement:
--   Let $p \ge 1$ be an integer, $e_p = (1 + 1/p)^p$, and put
--
--   $$\alpha = \frac{e_p}{e_p - 1}, \qquad \pi_k = (\alpha - 1)\left(\left(\frac{p+1}{p}\right)^{k-1} - 1\right) \quad (k = 1, \dots, p+1).$$
--
--   Then:
--   1. $\pi_{p+1} = 1$;
--   2. $0 \le \pi_1 \le \pi_2 \le \cdots \le \pi_p \le \pi_{p+1}$;
--   3. every constraint of the phase LP is tight: for every $k = 0, 1, \dots, p$,
--   $$\pi_{k+1}\, p + \sum_{i=1}^{k} (1 - \pi_i) = \alpha \cdot k .$$
--
--   Items 1 and 2 say that the $\pi_k$ are the cumulative probabilities of a phase-based randomized algorithm (the block is private by the $k$-th write with probability $\pi_k$); item 3 says that this algorithm's expected cost on every phase is exactly $\alpha$ times the optimal cost. This is the attainment half of the LP analysis in the proof of Theorem 4.
--
--   **Formalization Note** $\pi$ is a function $\mathbb{N} \to \mathbb{R}$ defined by the closed form for every $k$; the exponent $k-1$ is natural-number subtraction, which is only evaluated at $k \ge 1$ in the conclusions (the value $\pi_0$ is unused).
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), pp. 553–554, §3.2 (proof of Theorem 4), display for π_k and the paragraph 'A phase-based algorithm that achieves this competitive factor …'

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_ep

namespace NonuniformCompetitive.Snoopy

/-- The minimiser of the phase LP (Karlin et al. 1994, §3.2, pp. 553–554) is a valid
phase-based algorithm with every constraint tight. For `p ≥ 1`, put `α = e_p / (e_p − 1)` and
`π_k = (α − 1)(((p + 1)/p)^{k−1} − 1)`. Then `π_{p+1} = 1`, `0 ≤ π_1 ≤ π_2 ≤ ⋯ ≤ π_{p+1}`, and
for every `k = 0, …, p`, `π_{k+1} · p + ∑_{i=1}^{k} (1 − π_i) = α · k`.
The natural-number subtraction `k - 1` is only evaluated at `k ≥ 1` in the conclusion. -/
theorem lp_attained (p : ℕ) (hp : 1 ≤ p) (α : ℝ) (π : ℕ → ℝ)
    (hα : α = ep p / (ep p - 1))
    (hπ : ∀ k, π k = (α - 1) * ((((p : ℝ) + 1) / p) ^ (k - 1) - 1)) :
    π (p + 1) = 1 ∧ 0 ≤ π 1 ∧ (∀ k ∈ Finset.Icc 1 p, π k ≤ π (k + 1)) ∧
      ∀ k ≤ p, π (k + 1) * p + ∑ i ∈ Finset.Icc 1 k, (1 - π i) = α * k := by sorry

end NonuniformCompetitive.Snoopy
