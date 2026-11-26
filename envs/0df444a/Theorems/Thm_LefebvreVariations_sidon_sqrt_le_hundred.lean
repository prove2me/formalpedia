-- Prove2me | Theorems.Thm_LefebvreVariations_sidon_sqrt_le_hundred
-- name    : LefebvreVariations.sidon_sqrt_le_hundred
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:24:44.348005+00:00
-- url     : https://prove2.me/theorems/824d06af-eddf-420f-ade9-cfc1fe79278c
-- title:
--   Lefebvre's variations, No. 78 — on a theme by Erdős: Sidon sets in {1,...,N} have at least sqrt(N) elements for N up to 100
-- statement:
--   For every integer $N$ with $1\le N\le 100$, the largest size $h(N)$ of a Sidon set in $\{1,\dots,N\}$ satisfies
--   $$N\ \le\ h(N)^2,\qquad\text{i.e. } h(N)\ge\sqrt N .$$
--
--   A Sidon set is a set in which all pairwise sums $a+b$ are distinct (apart from the commutativity $a+b=b+a$). The case $N=100$ is tight: $h(100)=10$.
--
--   This is the lower-bound half of Erdős Problem 30, which asks whether $h(N)=\sqrt N+O(N^\varepsilon)$ for every $\varepsilon>0$, checked at its first hundred values.
--
--   **Formalization Note** `Erdos30.h N` is the maximum cardinality of a subset `B` of `Finset.Icc 1 N` with `Erdos30.IsSidon B`, defined as a supremum over the powerset, in the platform definitions `Def_Erdos30Basic`. The statement is `N ≤ Erdos30.h N ^ 2` for `1 ≤ N ≤ 100`; for `N = 0` it would also hold but is excluded.
--
--   **Why this is a variation.** This is a variation of Erdős Problem 30 on the platform, the open question of whether the largest Sidon set in $\{1,\dots,N\}$ has size $\sqrt N+O(N^\varepsilon)$. It is the lower-bound half at the first hundred sizes, in the parent's own definitions `Erdos30.h` and `Erdos30.IsSidon`, and every case is a finite explicit check (Golomb rulers). Settling it fixes the exact base values from which any asymptotic lower-bound argument starts.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Erdos Problem 30 (https://www.erdosproblems.com/30), Sidon sets in {1,...,N}; the lower bound h(N) >= (1+o(1))sqrt(N) goes back to Singer's perfect difference sets (J. Singer, A theorem in finite projective geometry and some applications to number theory, Trans. AMS 43 (1938)) and Erdos-Turan (1941) (titles and years cited from memory, not re-checked). For N <= 100 the statement follows from optimal Golomb rulers (OEIS A003022, cited from memory): a Sidon set of s elements fits in {1,...,N} as soon as N exceeds the length of an optimal s-mark ruler, and the needed lengths 1,3,6,11,17,25,34,44,55 for s=2..10 are all below (s-1)^2 + 1. Verified by exhaustive search while preparing this statement. Origin: the platform problem Erdos30.erdos_30 (Open), restricted to N <= 100 and to the lower-bound side.

import Definitions.Def_Erdos30Basic

set_option autoImplicit false

namespace LefebvreVariations

/-- The lower-bound half of Erdős Problem 30 at small size: for every `N` with `1 ≤ N ≤ 100`
there is a Sidon set in `{1,…,N}` of at least `√N` elements, i.e. `N ≤ h(N)²`. The case `N = 100` is
tight (`h(100) = 10`, as an optimal Golomb ruler with `10` marks has length `55`); the bound
follows from the optimal Golomb rulers tabulated in OEIS A003022 (cited from memory).
Source: Erdős Problem 30 (https://www.erdosproblems.com/30), and Erdős–Turán, "On a problem of
Sidon in additive number theory", J. London Math. Soc. 16 (1941), 212-215 (cited from memory). -/
theorem sidon_sqrt_le_hundred (N : ℕ) (h1 : 1 ≤ N) (h2 : N ≤ 100) :
    N ≤ Erdos30.h N ^ 2 := by
  sorry

end LefebvreVariations
