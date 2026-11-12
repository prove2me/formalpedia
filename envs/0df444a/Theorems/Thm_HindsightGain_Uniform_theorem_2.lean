-- Prove2me | Theorems.Thm_HindsightGain_Uniform_theorem_2
-- name    : HindsightGain.Uniform.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:32.790628+00:00
-- url     : https://prove2.me/theorems/2f04c7b3-c35c-4e82-a3af-dfa018e59d04
-- title:
--   Theorem 2 — Sharp uniform retention hindsight bound
-- statement:
--   Let $n,D\ge1$ and $r\ge2$ be integers. For each variable $i\in[n]$ let $K_i$ be a nonempty compact subset of the Euclidean unit ball in $\mathbb R^D$, with no convexity requirement. For every unordered $r$-element set $e$, let $A_e$ be an arbitrary multilinear interaction, and let $\|A\|_F$ be the Euclidean norm of all interaction coefficients, each interaction counted once. Write $\operatorname{Val}_A$ for the maximum of $\sum_eA_e(x_e)$ on $\prod_iK_i$, and $\operatorname{Val}_A(S)$ for the optimum keeping only interactions inside $S$.
--   For every $p\in(0,1]$, if $S_p$ retains variables independently with probability $p$, then
--   $$0\le\mathbb E\operatorname{Val}_A(S_p)-p^r\operatorname{Val}_A\le 8r\,2^{r/2}\,p^{r-1/2}\sqrt{1-p}\,n^{(r-1)/2}\|A\|_F.$$
--   The explicit constant is uniform in $n,D,K,A,p$. The statement includes $n<r$, negative optimal values, and $p=1$. It bounds the benefit of choosing an assignment after observing the restriction and is the full uniform-retention target of the mission.
--
--   Differences from the source:
--   - encoding: arbitrary multilinear interactions on r-element subsets of [n] and Euclidean local domains → coefficient arrays on cardinality-r Finsets of Fin n, with each interaction evaluated in increasing order in EuclideanSpace ℝ (Fin D); reason: orthonormal coordinates encode every source multilinear map uniquely, preserving its coefficient Frobenius norm and every compact local domain
--   - encoding: a maximum over the compact product domain → the real sSup of the actual polynomial image; reason: Model includes all source nonemptiness and compactness assumptions, so the image is nonempty, compact, bounded and has an attained maximum
--   - encoding: expectation over independent retention inside U or [n] → the finite sum over subsets S of U with mass p^|S| (1-p)^(|U|-|S|); reason: this is exactly the independent Bernoulli retention law, including p = 0 and p = 1 with the usual zeroth-power convention
--   - encoding: half-integer powers and an admissible constant C_r = 8r 2^(r/2) → real powers with exponents cast to ℝ before division, and the explicit constant 8r 2^(r/2); reason: the chosen constant is the source admissible value, uniformly for all models and p
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 2 (Uniform retention), p.20 (also p.5), proof pp.20–21

import Mathlib
import Definitions.Def_HindsightGain_Uniform_optima

set_option autoImplicit false

namespace HindsightGain.Uniform

/-- Theorem 2, pp.20-21 (also p.5), with the explicit admissible constant 8r 2^(r/2).
All n,D >= 1 and r >= 2 are allowed, including n < r; no convexity or sign assumption on A. -/
theorem theorem_2 {n D r : ℕ} (M : Model n D r) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ retentionMean M p - p ^ r * fullVal M ∧
      retentionMean M p - p ^ r * fullVal M ≤
        (8 * (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) *
          p ^ ((r : ℝ) - (1 : ℝ) / 2) * Real.sqrt (1 - p) *
            (n : ℝ) ^ (((r : ℝ) - 1) / 2) * frobenius M := by sorry

end HindsightGain.Uniform
