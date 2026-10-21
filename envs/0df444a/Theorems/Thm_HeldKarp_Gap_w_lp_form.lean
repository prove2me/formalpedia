-- Prove2me | Theorems.Thm_HeldKarp_Gap_w_lp_form
-- name    : HeldKarp.Gap.w_lp_form
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:47.561259+00:00
-- url     : https://prove2.me/theorems/5d23b573-c396-4f61-94ce-8e04e7b256c8
-- title:
--   §2, p. 1144 — $f$ depends only on $\pi_i-\pi_n$, and $w(\pi)=\min_x\{cx+\bar\pi(Ax-b)\mid A'x\le b',\ x\ge 0\}$
-- statement:
--   Let $n\ge 3$ and let $c_{ij}$ be real edge weights on $K_n$. Let $f$ be the gap function, $w(\pi)=\min_k[c_k+\sum_i\pi_i(d_{ik}-2)]$ the minimum over the 1-trees $k$, and $P$ the polyhedron $A'x\le b'$, $x\ge 0$ (constraints (ii)–(vi) of (3′)). Then:
--
--   1. $f(\pi)$ is independent of $\pi_1$ and depends only on the differences $\pi_i-\pi_n$, $i=2,\dots,n-1$: if $\pi,\pi'\in\mathbb R^n$ satisfy $\pi_i-\pi_n=\pi'_i-\pi'_n$ for $i=2,\dots,n-1$, then $f(\pi)=f(\pi')$.
--   2. For every $\pi$ with $\pi_1=\pi_n=0$, writing $\bar\pi=(\pi_2,\dots,\pi_{n-1})$,
--   $$
--   w(\pi)=\min_x\{cx+\bar\pi(Ax-b)\mid A'x\le b',\ x\ge 0\},
--   $$
--   where $(Ax)_i=\sum_{j>i}x_{ij}+\sum_{j<i}x_{ji}$ for $i=2,\dots,n-1$ and $b=(2,\dots,2)$; the minimum is attained.
--
--   Part 1 is what lets the maximization of $w$ be restricted to vectors with $\pi_1=\pi_n=0$; part 2 expresses $w$ as the value of a linear program over $P$, the form in which Theorem 2 is proved.
--
--   **Formalization Note** Part 2 asserts that $w(\pi)$ is the least element of the set of values $cx+\sum_{i=2}^{n-1}\pi_i(\deg_x(i)-2)$ over $x\in P$ (an attained minimum). $P$ uses the equalities $\sum_j x_{1j}=2$ and $\sum x_{ij}=n$ of (3′) and nonempty subsets $S$. $w$ is the published `HeldKarp.Ascent.oneTreeBound`. Vertex $1$ is `0 : Fin n`, vertex $n$ is `lastV n`.
-- source:
--   Held & Karp, The Traveling-Salesman Problem and Minimum Spanning Trees, Operations Research 18(6) 1970, p. 1144, §2 — f(π) is independent of π_1 and depends only on π_i − π_n; w(π) = min_x {cx + π̄(Ax − b) | A′x ≤ b′, x ≥ 0}

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
import Definitions.Def_HeldKarp_Gap_GapFunction
import Definitions.Def_HeldKarp_Gap_SubtourLP

open Classical
open HeldKarp.Ascent

namespace HeldKarp.Gap

/-- **§2, p. 1144 — the linear-programming form of `w(π)`** (Held & Karp 1970).
(1) `f(π)` is independent of `π_1` and depends only on the differences `π_i − π_n`,
`i = 2, …, n − 1`.
(2) For `π` with `π_1 = π_n = 0`, `w(π) = min_x {cx + π̄(Ax − b) | A′x ≤ b′, x ≥ 0}`, where
`π̄ = (π_2, …, π_{n−1})`, `Ax` is the vector of degrees of `x` at `2, …, n − 1` and `b = (2, …, 2)`;
the minimum is attained. -/
theorem w_lp_form {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) :
    (∀ π π' : Fin n → ℝ,
        (∀ i : Fin n, i ≠ 0 → i ≠ lastV n → π i - π (lastV n) = π' i - π' (lastV n)) →
        gap c π = gap c π') ∧
      (∀ π : Fin n → ℝ, π 0 = 0 → π (lastV n) = 0 →
        IsLeast ((fun x : Edge n → ℝ => cost c x +
            ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≠ 0 ∧ i ≠ lastV n),
              π i * (deg x i - 2)) '' OneTreePolyhedron n)
          (oneTreeBound c π)) := by sorry

end HeldKarp.Gap
