-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_3_2
-- name    : MemOracleLB.Optimization.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:39.124144+00:00
-- url     : https://prove2.me/theorems/18b2d5ef-cbdf-431a-befd-f5a518a08948
-- title:
--   Lemma 3.2 — Discarding unstable parts
-- statement:
--   Fix $0<t<1$ and the constants $0<c<1$, $C\ge1$ with the full Lemma 3.1 property at dimension $n$. Let $S$ be a family of positive-measure parts in a countable disjoint convex product partition of $E_n^{n-1}$. For each $P\in S$ let $u(P)$ be a fixed unit vector satisfying
--
--   $$\Pr(d_{\mathbb P}(v(A),u(P))\le t/C\mid A\in P)\ge1-1/1024.$$
--
--   There is a subfamily $B\subseteq S$ with total original Gaussian product measure at most $t/(2c)$ such that
--
--   $$\nu_{u(P)}<1/8\qquad(P\in S\setminus B).$$
--
--   On each retained part the rows have their independent Gaussian laws restricted to the factors. No additional regularity is imposed on those convex factors.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - encoding: n-1 rows in n dimensions → m rows in dimension m+1; reason: renaming n=m+1 avoids truncated natural subtraction and changes no positive-dimensional instance
--   - generalization: the constants selected in Lemma 3.1 and the standing sufficiently large dimension → any 0<c<1 and C>=1 satisfying the complete ShortResidualProperty at the given n>=2; reason: the source constants satisfy this property in the source range, and the discard argument uses only that property
--   - encoding: total measure of a family of parts → a countable sum of their original Gaussian measures in [0,infinity]; reason: the parts are disjoint and null-measurable, so the sum is exactly their union measure
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 3.2, PDF p. 12 (printed p. 11), continues on PDF p. 13, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Partitions

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace MemOracleLB.Optimization

/-- Lemma 3.2, PDF pp.12–13 (printed pp.11–12).
The constants are bound to Lemma 3.1's property at this dimension. -/
theorem lemma_3_2 {m : ℕ} (hm : 1 ≤ m) (c C : ℝ)
    (hc : 0 < c) (hc1 : c < 1) (hC : 1 ≤ C) (hshort : ShortResidualProperty m c C)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) {ι : Type} [Countable ι]
    (P : ConvexProductPartition ι m (m + 1)) (S : Set ι)
    (hpos : ∀ p ∈ S, 0 < rowLaw m (m + 1) (P.part p))
    (u : ι → E (m + 1)) (hloc : Localizes P S u (t / C)) :
    ∃ B : Set ι, B ⊆ S ∧ P.mass B ≤ ENNReal.ofReal (t / (2 * c)) ∧
      ∀ p ∈ S \ B, projectedFlip (P.partLaws p) (u p) < 1 / 8 := by sorry

end MemOracleLB.Optimization
