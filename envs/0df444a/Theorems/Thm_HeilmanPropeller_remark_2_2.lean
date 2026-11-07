-- Prove2me | Theorems.Thm_HeilmanPropeller_remark_2_2
-- name    : HeilmanPropeller.remark_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:15.737161+00:00
-- url     : https://prove2.me/theorems/b59c3805-21db-49a2-8393-f900456a7995
-- title:
--   Remark 2.2: cells of an optimal partition have measure at most $1/2$
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   Let $n\ge1$, $N\ge2$, and let $\mathcal A=(A_1,\dots,A_k)$, $k\le N$, be a partition of $\mathbb R^n$ maximizing $F$ among partitions of $\mathbb R^n$ into $N$ sets, with $\gamma_n(A_i)>0$ for all $i$ (the setting of Lemma 2.1). Then
--
--   $$p_i=\gamma_n(A_i)\le\tfrac12\qquad\text{for all }1\le i\le k.$$
--
--   The bound is used in Lemma 5.1 and in Step 3 of Lemma 5.2.
--
--   **Formalization Note** $p_i$ is the real-valued measure `(gaussian n).real (A i)`.
--
--   Differences from the source:
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - encoding: maximizing F among partitions of ℝⁿ into N sets → MaximizesAmong N A, competitors are N-cell IsPartitions (a.e.-partitions); reason: a null modification changes no moment, so the maximum over a.e.-partitions is the paper's maximum
--   - reading: "(2.2) implies that pᵢ ≤ 1/2 for all 1 ≤ i ≤ k" → stated in the setting of Lemma 2.1 (maximizer, positive cells, n ≥ 1, N ≥ 2); reason: the remark follows Lemma 2.1 and refers to its k and its cells
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), Remark 2.2, p.5

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanPropeller_MaximizesAmong

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller

/-- **Remark 2.2 (cells have measure at most one half).** Heilman, *On the Propeller Conjecture*,
arXiv:2610.32158 (held version, sha256 13f5ddf8…), Remark 2.2, p.5.

In the setting of Lemma 2.1 (`n ≥ 1`, `N ≥ 2`, `A = (A₁, …, A_k)` maximizing `F` among partitions
of `ℝⁿ` into `N` sets, `γₙ(Aᵢ) > 0` for all `i`), the cone description (2.2) implies
`pᵢ = γₙ(Aᵢ) ≤ 1/2` for every `i`.

**Formalization Note.** `MaximizesAmong N A` is Lemma 2.1's hypothesis (an `IsPartition` into
`k ≤ N` cells maximizing `F` among `N`-cell partitions); `pᵢ` is `(gaussian n).real (A i)`. -/
theorem remark_2_2 (n N : ℕ) (hn : 1 ≤ n) (hN : 2 ≤ N) (k : ℕ) (A : Fin k → Set (Space n))
    (hA : MaximizesAmong N A) (hpos : ∀ i, 0 < gaussian n (A i)) :
    ∀ i, (gaussian n).real (A i) ≤ 1 / 2 := by sorry

end HeilmanPropeller
