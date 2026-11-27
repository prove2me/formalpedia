-- Prove2me | Theorems.Thm_LefebvreVariations_binomial_at_least_mean_le_six
-- name    : LefebvreVariations.binomial_at_least_mean_le_six
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:29:09.862435+00:00
-- url     : https://prove2.me/theorems/ba79d58c-704c-5dfb-82fd-53f630d61a4e
-- title:
--   Lefebvre's variations, No. 278 — on a theme by Rigollet and Tong: a binomial variable with at most six trials reaches its mean with probability at least min(q, 1/4)
-- statement:
--   Let $1\le n\le 6$ be an integer and let $q\in(0,\tfrac12]$. Then
--   $$
--   \sum_{\substack{0\le j\le n\\ j\ge nq}}\binom nj\,q^{j}(1-q)^{n-j}\ \ge\ \min\bigl(q,\tfrac14\bigr).
--   $$
--   Equivalently, a binomial variable $N\sim\mathrm{Bin}(n,q)$ satisfies $\Pr\{N\ge nq\}\ge\min(q,1/4)$.
--
--   A binomial variable reaches its mean with probability bounded below by a constant, here $\min(q,1/4)$, for every $n$ and $q\le\frac12$; this is the form needed in lower-bound arguments for Neyman–Pearson classification. For $n=1$ the left side equals $q$, and for $n\ge2$ the left side strictly exceeds the right side on $(0,\frac12]$.
--
--   **Formalization Note** The left side is the parent's `NeymanPearsonClassification.binomTail n q (n * q)` (imported from the parent's definitions): the sum over `j ∈ range (n + 1)` with `(n : ℝ) * q ≤ j` of `(n.choose j) * q ^ j * (1 - q) ^ (n - j)`, with the real threshold `t = n * q`, so the endpoint `j = nq` (when `nq` is an integer) is included. The cases `n ≤ 6` are quantified inside the statement (`1 ≤ n` and `n ≤ 6`).
--
--   **Why this is a variation.** A variation on the open platform problem NeymanPearsonClassification.binomial_at_least_mean (Lemma 6.4 of Rigollet and Tong: P(Bin(n,q) >= nq) >= min(q, 1/4) for every n >= 1 and q <= 1/2), restricted to n <= 6. It uses the parent's own definition `binomTail`. It is a special case of the parent (same conclusion, hypothesis n <= 6 added).
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750, Lemma 6.4 (location as recorded by the platform's parent statement, not re-read). Checked here in exact rational arithmetic for n = 1,...,6 on the grid q = i/20000 (0 < q <= 1/2) and at the break points q = k/n and at q = k/n plus or minus 1e-9 and 1e-12: the left side minus min(q,1/4) is never negative; it is 0 for n = 1 (both sides equal q when q <= 1/4 and the left side q exceeds 1/4 otherwise) and strictly positive for n >= 2 (tending to 0 as q tends to 0).

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

set_option autoImplicit false

namespace LefebvreVariations

open NeymanPearsonClassification

/-- A binomial variable with `n ≤ 6` trials and success probability `q ∈ (0, 1/2]` reaches its mean `n q` with probability at least `min(q, 1/4)`.
Here `binomTail n q t = P(N ≥ t)` for `N ∼ Bin(n, q)`, as in the parent. For `n = 1` the tail is exactly `q`; for `n ≥ 2` it exceeds `min(q, 1/4)` by a positive margin on `(0, 1/2]`.
Source: Rigollet and Tong, *Neyman-Pearson classification, convexity and stochastic constraints*, arXiv:1102.5750, Lemma 6.4, as recorded by the platform (not re-read); the cases `n ≤ 6` were also checked numerically. -/
theorem binomial_at_least_mean_le_six (n : ℕ) (hn1 : 1 ≤ n) (hn6 : n ≤ 6) (q : ℝ)
    (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    min q (1 / 4) ≤ binomTail n q (n * q) := by
  sorry

end LefebvreVariations
