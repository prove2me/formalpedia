-- Prove2me | Theorems.Thm_MinSumFPT_lemma_9
-- name    : MinSumFPT.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:53.552141+00:00
-- url     : https://prove2.me/theorems/e21249af-a20e-4e90-88e0-524df7c2d5c0
-- title:
--   Lemma 9 — uniform sampling $(0,3)$-covers a largest cluster
-- statement:
--   Let $d$ be a pseudometric on $A$ with $|A|=n$, and let $\sigma$ be a clustering into $k\ge1$ clusters sorted by non-increasing size, so that $C_1$ is a largest cluster. Let $\delta>0$ and let $M$ be a set of $m$ points sampled independently and uniformly at random with replacement. If
--
--   $$
--   m\ \ge\ 2k\cdot\ln(k/\delta),
--   $$
--
--   then with probability at least $1-\delta/k$ the set $M$ $(0,3)$-covers $C_1$.
--
--   This is the base case of the inductive argument behind Theorem 5: the uniform sample at the root of the sampling tree already contains a good center for a largest cluster.
--
--   **Formalization Note** The sample is a uniformly random tuple in $A^m$, so the probability is the fraction of the $n^m$ tuples whose image covers $C_1$.
--
--   Differences from the source:
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
--   - encoding: m points sampled independently and uniformly with replacement → the fraction of tuples s : Fin m → Fin n whose image covers C₁; reason: the uniform law on tuples is the i.i.d. uniform sample
--   - encoding: C₁ a largest cluster, clusters sorted by non-increasing size → label 0 of a labelling with antitone cluster sizes; reason: 0-based labels
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 9, p.13

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumFPT_IsCovered

open scoped Classical

namespace MinSumFPT

/-- Lemma 9 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 9, p.13): let the clusters of `σ` be sorted by non-increasing size,
so that `C₁` (label `0`) is a largest cluster. If `m ≥ 2k ⋅ ln(k/δ)`, then a set `M` of `m`
points sampled independently and uniformly at random with replacement (0, 3)-covers `C₁` with
probability at least `1 − δ/k`.

**Formalization Note.** The sample is a tuple `s : Fin m → Fin n`, uniform over the `n^m` tuples,
and `M` is its image; the probability is the fraction of tuples. With ε = 0 the OPT term of (1)
vanishes (OPT is put as `optCost d k`). -/
theorem lemma_9 {n k : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsPseudometric d)
    (hk : 0 < k) (σ : Fin n → Fin k)
    (hsort : ∀ i j : Fin k, i ≤ j → (clusterOf σ j).card ≤ (clusterOf σ i).card)
    (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 2 * (k : ℝ) * Real.log (k / δ) ≤ m) :
    (1 - δ / k) * (n : ℝ) ^ m ≤
      ((Finset.univ.filter (fun s : Fin m → Fin n =>
        IsCovered d (optCost d k) k 0 3 (Finset.univ.image s) (clusterOf σ ⟨0, hk⟩))).card : ℝ) := by sorry

end MinSumFPT
