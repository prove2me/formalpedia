-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_1_5
-- name    : MemOracleLB.Optimization.lemma_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:49.429425+00:00
-- url     : https://prove2.me/theorems/58f39c67-57b4-4558-af2e-85d4932ccec0
-- title:
--   Lemma 1.5 — Normal-localizing product partition
-- statement:
--   There are absolute $a>0$ and $0<c<1$ such that, for every sufficiently large $n$ and every $\eta\in(0,1)$, the following holds. Let $\mathcal P$ be a countable disjoint partition of $E_n^{n-1}$ into convex product parts. Let $S_{\rm loc}$ be a family of total original $\bar\gamma_n^{\otimes(n-1)}$ measure at least $\eta$. Suppose each positive-measure $P\in S_{\rm loc}$ has a fixed unit $u(P)$ with
--
--   $$\Pr(d_{\mathbb P}(v(A),u(P))\le c\eta\mid A\in P)\ge1-1/1024.$$
--
--   There is $S'\subseteq S_{\rm loc}$ of total measure at least $\eta/2$ such that every retained part satisfies
--
--   $$\bar\gamma_n^{\otimes(n-1)}(P)\le\exp(-an^2/\log n).$$
--
--   All countable partitions and all convex factors are included. No finiteness, Borel or closedness requirement is added. The per-dimension property contains exactly these hypotheses and both conclusions.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - encoding: n-1 rows in n dimensions → m rows in dimension m+1; reason: renaming n=m+1 avoids truncated natural subtraction and changes no positive-dimensional instance
--   - encoding: the standing sufficiently large absolute ambient dimension on PDF p.8 → an existential natural threshold N at least 2 before the dimension and all instance data; reason: this makes the source asymptotic quantifier explicit and keeps logarithms and denominators in their stated domains
--   - encoding: a countable family and its total measure → an arbitrary countable index type and a tsum of nonnegative extended masses; reason: disjointness and coverage are actual partition conditions, with no restriction to finitely many parts
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 1.5, PDF p. 5 (printed p. 4), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Partitions

namespace MemOracleLB.Optimization

/-- Lemma 1.5, PDF p.5 (printed p.4), at full strength for countable partitions. -/
theorem lemma_1_5 : ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ c < 1 ∧
    ∃ N : ℕ, 2 ≤ N ∧ ∀ m : ℕ, N ≤ m + 1 → LocalizingPartitionProperty m a c := by sorry

end MemOracleLB.Optimization
