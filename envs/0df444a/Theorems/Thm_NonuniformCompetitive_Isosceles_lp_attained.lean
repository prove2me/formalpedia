-- Prove2me | Theorems.Thm_NonuniformCompetitive_Isosceles_lp_attained
-- name    : NonuniformCompetitive.Isosceles.lp_attained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:55:32.787985+00:00
-- url     : https://prove2.me/theorems/a8f82681-cd73-4713-959a-9cdbbb8ebb9a
-- title:
--   §5, p. 566 — the minimising $\pi_k=(\alpha-1)((2d/(2d-1))^k-1)$ are monotone probabilities and make every phase constraint tight
-- statement:
--   Let $d\ge1$ be an integer, let
--   $$\alpha=\frac{e_{2d-1}+1/4d}{(e_{2d-1}-1)+1/2d},\qquad e_{2d-1}=\left(\frac{2d}{2d-1}\right)^{2d-1},$$
--   and define
--   $$\pi_k=(\alpha-1)\left(\left(\frac{2d}{2d-1}\right)^k-1\right)\quad(1\le k\le 2d-1),\qquad \pi_{2d}=1.$$
--   Then
--   1. $0\le\pi_1\le\pi_2\le\cdots\le\pi_{2d-1}\le\pi_{2d}=1$;
--   2. every phase constraint of the LP holds with equality at this $\alpha$:
--   $$(\pi_k)\,2d+\sum_{i=1}^{k}(1-\pi_i)=\alpha k\quad(1\le k<2d),\qquad 2d+\sum_{i=1}^{2d-1}(1-\pi_i)+\tfrac12=\alpha\cdot 2d.$$
--
--   Item 1 says the $\pi_k$ are valid, nondecreasing covering probabilities, so a lazy phase-based algorithm with these probabilities exists; item 2 says its expected cost on every phase is exactly $\alpha$ times the off-line cost of the phase. Together with the LP lower bound, it shows that $\alpha$ is the minimum of the phase LP.
--
--   **Formalization Note** $\pi$ is any function $\mathbb N\to\mathbb R$ agreeing with the closed form on $1\le k\le 2d-1$ and equal to $1$ at $2d$; its other values are unused.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 566, §5, proof of Theorem 12: closed form of $\pi_k$ and the claim $0\le\pi_1\le\cdots\le\pi_{2d}=1$; equalities (*) on p. 565 and "By setting this to an equality" on p. 566

import Mathlib
import Definitions.Def_NonuniformCompetitive_Isosceles_isoscelesRatio

namespace NonuniformCompetitive.Isosceles

/-- §5, p. 566 (Karlin–Manasse–McGeoch–Owicki 1994): the minimiser of the phase LP is a valid
probability schedule. Let `1 ≤ d` and `α = isoscelesRatio d`. If
`π_k = (α - 1) ((2d/(2d-1))^k - 1)` for `1 ≤ k ≤ 2d - 1` and `π_{2d} = 1`, then
`0 ≤ π_1 ≤ π_2 ≤ ⋯ ≤ π_{2d} = 1`, and every constraint of the phase LP holds with equality:
`2d · π_k + ∑_{i=1}^{k} (1 - π_i) = α k` for `1 ≤ k < 2d`, and
`2d + ∑_{i=1}^{2d-1} (1 - π_i) + 1/2 = α · 2d`. -/
theorem lp_attained (d : ℕ) (hd : 1 ≤ d) (π : ℕ → ℝ)
    (hπ : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d - 1 →
      π k = (isoscelesRatio d - 1) * (((2 * d : ℝ) / (2 * d - 1)) ^ k - 1))
    (hπ2d : π (2 * d) = 1) :
    0 ≤ π 1 ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → π k ≤ π (k + 1)) ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d →
      π k * (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 k, (1 - π i) = isoscelesRatio d * (k : ℝ)) ∧
    (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 (2 * d - 1), (1 - π i) + 1 / 2
      = isoscelesRatio d * (2 * d : ℝ) := by sorry

end NonuniformCompetitive.Isosceles
