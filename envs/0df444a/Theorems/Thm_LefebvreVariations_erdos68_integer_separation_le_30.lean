-- Prove2me | Theorems.Thm_LefebvreVariations_erdos68_integer_separation_le_30
-- name    : LefebvreVariations.erdos68_integer_separation_le_30
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:52:21.488355+00:00
-- url     : https://prove2.me/theorems/8c1350cb-7bd2-4cd9-9485-5e06df7dc988
-- title:
--   Lefebvre's variations, No. 23 — on a theme by Erdős: the integer separation of Erdős Problem 68 for $M\le 30$
-- statement:
--   This verifies the integer-separation step of Erdős Problem 68 for $3\le M\le30$.
--
--   Let $x=\sum_{n\ge2}\frac1{n!-1}$. For every $M$ with $3\le M\le30$ and every integer $m$,
--
--   $$
--   \big|M!\,x-m\big|\ \ge\ \frac1{M(M+1)} .
--   $$
--
--   Erdős asked whether $x$ is irrational; the parent statement is the quantitative separation that would follow the classical proof of the irrationality of $e$. Here it is established for $3\le M\le30$ from a rigorous enclosure of $x$: the partial sum up to $n=40$ is computed exactly and the tail is bounded by $4/41!$ by comparison with a geometric series.
--
--   **Formalization Note** The series and the separation are the parent's; the margin is smallest in relative terms at $M=4$.
--
--   **Why this is a variation.** This varies Erdős problem 68 on the platform, the irrationality of $\sum_{n\ge 2} 1/(n!-1)$. It is an unconditional partial result: for $3\le M\le 30$ the number $M!\sum_{n\ge2}1/(n!-1)$ stays at distance at least $1/(M(M+1))$ from every integer, a finite range of Fourier's factorial-multiple irrationality criterion. Extending it to all $M$ would prove the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   P. Erdős, On the irrationality of certain series: problems and results, in New Advances in Transcendence Theory (Durham, 1986), A. Baker (ed.), Cambridge Univ. Press, 1988, 102–109; problem page https://www.erdosproblems.com/68. The range 3 ≤ M ≤ 30 is an explicit verification. Parent problem: Erdos68.factorial_moment_integer_separation.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- **Erdős 68 integer separation for `3 ≤ M ≤ 30`**: for these `M`, no integer lies within
`1 / (M (M + 1))` of `M! · Σ_{n ≥ 2} 1/(n! − 1)` (the fractional parts, computed from the partial
sum up to `n = 40` plus the tail `< 2/41!`, stay in `[0.039, 0.961]`). This is the finite range
of the factorial-multiple form of Fourier's irrationality criterion for Erdős's constant
`1.2216…`; Erdős, *On the irrationality of certain series: problems and results*, in
*New Advances in Transcendence Theory* (CUP 1988) 102–109; erdosproblems.com/68. -/
theorem erdos68_integer_separation_le_30 (M : ℕ) (hM : 3 ≤ M) (hM30 : M ≤ 30) (m : ℤ) :
    1 / ((M : ℝ) * ((M : ℝ) + 1)) ≤
      |((M.factorial : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1))) - (m : ℝ)| := by
  sorry

end LefebvreVariations
