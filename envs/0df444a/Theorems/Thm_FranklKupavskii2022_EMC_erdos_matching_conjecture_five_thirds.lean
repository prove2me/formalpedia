-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_erdos_matching_conjecture_five_thirds
-- name    : FranklKupavskii2022.EMC.erdos_matching_conjecture_five_thirds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:23:54.293802+00:00
-- url     : https://prove2.me/theorems/388d4e63-5e37-4212-9b26-f3113c7fb8d6
-- title:
--   Theorem 1: the Erdős Matching Conjecture for $n\ge\frac53sk-\frac23s$ and $s\ge s_0$
-- statement:
--   There is an absolute constant $s_0$ such that for all integers $k\ge1$, $s\ge s_0$ and $n$ with
--
--   $$
--   n\ge\frac53sk-\frac23s,
--   $$
--
--   the largest family of $k$-element subsets of $[n]$ with no $s+1$ pairwise disjoint members has
--
--   $$
--   m(n,k,s)=\binom nk-\binom{n-s}k \tag{6}
--   $$
--
--   members. The bound is attained by the family of all $k$-sets meeting a fixed $s$-element set. This settles the Erdős Matching Conjecture in this range, improving the earlier range $n\ge(2s+1)k-s$ of Frankl (2013).
--
--   **Formalization Note** The equality asserts both the upper bound and its attainment. $s_0$ is chosen before $n$, $k$ and $s$. The standing assumption $n\ge k(s+1)$ of Sect. 1 is not a hypothesis: it follows from the threshold when $k\ge2$ and $s\ge3$, and for $k=1$ (6) holds for every $n\ge s$.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Theorem 1, p. 2

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_emcMax

namespace FranklKupavskii2022.EMC

/-- Theorem 1 (Frankl–Kupavskii, *The Erdős Matching Conjecture and concentration inequalities*,
arXiv:1806.08855v3, p. 2): there exists an absolute constant `s_0` such that
`m(n, k, s) = \binom{n}{k} − \binom{n−s}{k}` (6) holds if `n ≥ \frac{5}{3}sk − \frac{2}{3}s` and
`s ≥ s_0`.

**Formalization Note.** `m(n, k, s)` is `emcMax n k s`, the largest size of a family of `k`-subsets
of `[n] = {1, …, n}` with no `s + 1` pairwise disjoint members; the equality states both the upper
bound and its attainment. `s_0` is chosen before `n`, `k`, `s` (absolute). The threshold is
compared in `ℝ`. `k ≥ 1` is the standing "positive integers" assumption (at `k = 0`, (6) fails).
The Sect. 1 assumption `n ≥ k(s + 1)` is not a binder: for `k ≥ 2` and `s ≥ 3` it follows from the
threshold, and at `k = 1` (6) holds for every `n ≥ s`. The natural subtraction is exact since
`\binom{n−s}{k} ≤ \binom{n}{k}`. -/
theorem erdos_matching_conjecture_five_thirds :
    ∃ s₀ : ℕ, ∀ n k s : ℕ, 1 ≤ k → s₀ ≤ s →
      (5 / 3 : ℝ) * s * k - (2 / 3) * s ≤ n →
      emcMax n k s = n.choose k - (n - s).choose k := by sorry

end FranklKupavskii2022.EMC
