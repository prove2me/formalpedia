-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_Supplement_all_clauses_extremal
-- name    : MajorityDepthThree.Exact.Supplement.all_clauses_extremal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:17:44.093807+00:00
-- url     : https://prove2.me/theorems/686e2562-6651-49ff-acb4-f56fc70418f6
-- title:
--   Fact 3.12 — all (k−i+1)-clauses form a t-extremal k-CNF, $\Theta(n,t,k)=\binom nt$
-- statement:
--   Let $n,k\ge1$ and $1\le i\le k$ with $t=n-k+i\ge0$. Let $V$ be a set of $n$ variables and $F$ the CNF consisting of all positive clauses on $k-i+1$ variables of $V$. Then $F$ is monotone and $(k-i+1)$-uniform, it is a $t$-extremal $k$-CNF — a valid $t$-threshold CNF of width at most $k$ whose number of $t$-transversals equals the maximum $\Theta(n,t,k)$ over **all** $t$-threshold CNFs of width at most $k$ on $V$, negative literals allowed — and
--
--   $$\Theta(n,t,k)=\binom nt .$$
--
--   For $k=3$ this gives the second line of Theorem 3.10, $\Phi_0(s,t)=\binom{3t-s}{t}$ when $2t-2\le s\le 2t$. The competitor class is all width-$k$ CNFs, wider than in Fact 3.2, where competitors have the clique's own width.
--
--   Differences from the source:
--   - encoding: n variables, t = n − k + i → the carrier Fin n with V = univ, and t written as the natural number n + i − k under k ≤ n + i; reason: relabeling changes nothing; k ≤ n + i is exactly t ≥ 0, so no truncation occurs
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.10, Fact 3.12 (with Definition 2.6, p.7)

import Definitions.Def_MajorityDepthThree_Exact_Supplement_Constructions

set_option autoImplicit false

namespace MajorityDepthThree.Exact.Supplement

open MajorityDepthThree.Exact

/-- Fact 3.12 (p. 10): for `n, k ≥ 1`, `1 ≤ i ≤ k` and `t = n - k + i ≥ 0`, the monotone
CNF of all `(k - i + 1)`-clauses on `n` variables is `(k - i + 1)`-uniform and
`t`-extremal among all (signed) `t`-threshold `k`-CNFs on `n` variables, and
`Θ(n, t, k) = binom(n, t)`. Here `t` is written `n + i - k` (no truncation since
`k ≤ n + i`). -/
theorem all_clauses_extremal (n k i : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hi : 1 ≤ i)
    (hik : i ≤ k) (hkn : k ≤ n + i) :
    let V : Finset (Fin n) := Finset.univ
    let F := clique V (k - i + 1)
    Monotone F ∧ Uniform (k - i + 1) F ∧ Extremal V F (n + i - k) k ∧
      thetaMax V (n + i - k) k = Nat.choose n (n + i - k) := by sorry

end MajorityDepthThree.Exact.Supplement
