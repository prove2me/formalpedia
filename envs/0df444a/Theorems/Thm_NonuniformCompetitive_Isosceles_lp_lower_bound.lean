-- Prove2me | Theorems.Thm_NonuniformCompetitive_Isosceles_lp_lower_bound
-- name    : NonuniformCompetitive.Isosceles.lp_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:54:50.927418+00:00
-- url     : https://prove2.me/theorems/751255bf-986b-4950-a6c3-7430868a93cb
-- title:
--   §5, pp. 565–566 — every feasible point of the 1-d-d phase LP has $\alpha\ge(e_{2d-1}+1/4d)/((e_{2d-1}-1)+1/2d)$
-- statement:
--   Let $d\ge1$ be an integer, let $\pi_1,\dots,\pi_{2d-1}$ be arbitrary real numbers and let $\alpha$ be a real number. Suppose the phase constraints of the two-server problem on the $1$-$d$-$d$ isosceles triangle hold:
--   $$(\pi_k)\,2d+\sum_{i=1}^{k}(1-\pi_i)\le\alpha\cdot k\qquad(1\le k<2d),$$
--   $$2d+\sum_{i=1}^{2d-1}(1-\pi_i)+\tfrac12\le\alpha\cdot 2d.$$
--   Then
--   $$\alpha\ge\frac{e_{2d-1}+1/4d}{(e_{2d-1}-1)+1/2d},\qquad e_{2d-1}=\left(\frac{2d}{2d-1}\right)^{2d-1}.$$
--
--   In the paper, $\pi_k$ is the probability that a phase-based on-line algorithm covers both $a$ and $b$ after the $k$-th request of a phase of alternating requests to $a$ and $b$; the left-hand sides are its expected costs on the phase $\sigma_k$ (the $k$ alternating requests, then a request at $c$ and possibly one more at $a$ or $b$), and $k$, resp. $2d$, is the optimal off-line cost of that phase. The statement says that no choice of the $\pi_k$ gives an LP bound below the ratio of Theorem 12; together with the paper's Theorem 3 this is the lower-bound half of Theorem 12.
--
--   **Formalization Note** The $\pi_k$ are free real variables, as in the paper ("we permit the $\pi_k$ to be free variables"); no constraint $0\le\pi_k\le1$ is imposed, which makes the statement stronger. $\pi$ is a function $\mathbb N\to\mathbb R$ whose values at $0$ and at indices $\ge 2d$ are unused.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, pp. 565–566, §5, proof of Theorem 12: the constraint system on p. 565 and the displayed bound for $\alpha$ on p. 566

import Mathlib
import Definitions.Def_NonuniformCompetitive_Isosceles_isoscelesRatio

namespace NonuniformCompetitive.Isosceles

/-- §5, pp. 565–566 (Karlin–Manasse–McGeoch–Owicki 1994): the phase LP for the two-server problem
on the `1`-`d`-`d` isosceles triangle. For `1 ≤ d`, any real numbers `π 1, …, π (2d-1)` (free,
not restricted to `[0,1]`) and any `α` satisfying the `2d` phase constraints
* `2d · π_k + ∑_{i=1}^{k} (1 - π_i) ≤ α · k` for `1 ≤ k < 2d`, and
* `2d + ∑_{i=1}^{2d-1} (1 - π_i) + 1/2 ≤ α · 2d`,
have `α ≥ (e_{2d-1} + 1/(4d)) / ((e_{2d-1} - 1) + 1/(2d))`.
The values of `π` at `0` and at indices `≥ 2d` are unused. -/
theorem lp_lower_bound (d : ℕ) (hd : 1 ≤ d) (π : ℕ → ℝ) (α : ℝ)
    (hlt : ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      π k * (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 k, (1 - π i) ≤ α * (k : ℝ))
    (hge : (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 (2 * d - 1), (1 - π i) + 1 / 2 ≤ α * (2 * d : ℝ)) :
    isoscelesRatio d ≤ α := by sorry

end NonuniformCompetitive.Isosceles
