-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_corollary_1_6
-- name    : MemOracleLB.Optimization.corollary_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:49.432181+00:00
-- url     : https://prove2.me/theorems/afb2334d-b0ed-45f2-82a9-45cff8dd1bb5
-- title:
--   Corollary 1.6 — Decision-tree depth
-- statement:
--   Choose absolute witnesses $a>0$ and $0<c_{\rm loc}<1$ satisfying the full Lemma 1.5 property in every sufficiently large dimension. There is an absolute $c>0$ such that for every $\eta\in(0,1)$ there is a threshold $n_\eta\ge2$ with the following property. Suppose $n\ge n_\eta$ and the convex product parts are exactly the leaf sets of a deterministic decision tree having at most $2n+1$ responses per query. Suppose a family of mass at least $\eta$ satisfies the Lemma 1.5 localization hypothesis with that same $c_{\rm loc}$. Its actual query depth $T$ satisfies
--
--   $$\Pr\!\left(T\ge c\frac{n^2}{\log^2 n}\right)\ge\eta/4.$$
--
--   The witnesses $a,c_{\rm loc},c$ are independent of $\eta$, the tree and the dimension. The statement exports the Lemma 1.5 witnesses together with their full property, so its localization constant is bound to that lemma. Leaf counts are not assumed.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - encoding: n-1 rows in n dimensions → m rows in dimension m+1; reason: renaming n=m+1 avoids truncated natural subtraction and changes no positive-dimensional instance
--   - encoding: the constants and hypotheses of Lemma 1.5 referenced by the corollary → jointly quantified witnesses carrying the full per-dimension Lemma 1.5 property and the tree-depth conclusion; reason: independent draft theorems cannot import one another, so the common witnesses are exported rather than replaced by an unrelated constant
--   - encoding: at most 2n+1 possible responses and its reached leaf sets → response labels in Fin(2n+1), actual path consistency and a leaf-set equality with the partition; reason: smaller alphabets embed in this one, and no shallow-leaf counting conclusion is assumed
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Corollary 1.6, PDF p. 6 (printed p. 5), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Partitions

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace MemOracleLB.Optimization

/-- Corollary 1.6, PDF p.6 (printed p.5). The localization constant is exported together
with its Lemma 1.5 property; it is not a fresh unrelated parameter. -/
theorem corollary_1_6 : ∃ a cLoc c : ℝ, 0 < a ∧ 0 < cLoc ∧ cLoc < 1 ∧ 0 < c ∧
    (∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ m : ℕ, N₀ ≤ m + 1 → LocalizingPartitionProperty m a cLoc) ∧
    ∀ η : ℝ, 0 < η → η < 1 → ∃ N : ℕ, 2 ≤ N ∧
      ∀ m : ℕ, N ≤ m + 1 → ∀ {Q : Type}
        (D : DecisionTree (Fin m → E (m + 1)) Q (2 * (m + 1) + 1))
        (P : ConvexProductPartition (List (Fin (2 * (m + 1) + 1))) m (m + 1)),
        IsLeafPartition D P → ∀ (S : Set (List (Fin (2 * (m + 1) + 1))))
          (u : List (Fin (2 * (m + 1) + 1)) → E (m + 1)),
          ENNReal.ofReal η ≤ P.mass S → Localizes P S u (cLoc * η) →
          rowLaw m (m + 1) {x | ENNReal.ofReal (c * (m + 1 : ℝ) ^ 2 /
            (Real.log (m + 1)) ^ 2) ≤ (D.depth x).toENNReal} ≥
            ENNReal.ofReal (η / 4) := by sorry

end MemOracleLB.Optimization
