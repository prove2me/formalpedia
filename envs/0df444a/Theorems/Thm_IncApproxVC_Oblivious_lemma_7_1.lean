-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_lemma_7_1
-- name    : IncApproxVC.Oblivious.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:41:56.459567+00:00
-- url     : https://prove2.me/theorems/5770e02d-0173-4409-aca6-eb88604aba6a
-- title:
--   Lemma 7.1 — UnbiasedSample: $\lceil 10(n/k)\log n\rceil$ uniform vertex samples hit every set of size $\ge k$ w.p. $\ge 1-n^{-10}$
-- statement:
--   Let $V$ be a finite set of $n$ vertices and fix a size parameter $k\ge 1$. Sample
--   $$N=\Big\lceil 10\,\frac{n}{k}\,\log_2 n\Big\rceil$$
--   vertices of $V$ independently and uniformly at random, with replacement, and let $T$ be the set of samples. Then for every $A\subseteq V$ with $|A|\ge k$,
--   $$\Pr[T\cap A\neq\emptyset]\ \ge\ 1-n^{-10}.$$
--   Algorithm 3 uses it to find a vertex on the right side of a vertex cut whose right side is large.
--
--   **Formalization Note.** The probability is the fraction of sequences $\sigma\in V^N$ that contain a vertex of $A$; logarithms are base 2 (p. 2).
--
--   Differences from the source:
--   - encoding: Pr over N vertices sampled uniformly with replacement → the fraction of sequences σ : Fin N → V containing a vertex of A; reason: uniform sampling with replacement is the uniform law on V^N
--   - encoding: size parameter k ≥ 1 → k : ℝ with 1 ≤ k; reason: the paper calls it with non-integer k = n − (1+ε)κ (Algorithm 3, line 9); integers are a special case
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 23, Lemma 7.1

import Mathlib

namespace IncApproxVC.Oblivious

/-- **Lemma 7.1** (`UnbiasedSample(G, k)`), p. 23. Fix a size parameter `k ≥ 1`. Sampling
`⌈10 (n/k) log₂ n⌉` vertices of `V` independently and uniformly at random with replacement gives a
set `T` with `Pr[T ∩ A ≠ ∅] ≥ 1 − n^{−10}` for every `A ⊆ V` with `|A| ≥ k`. The probability is the
fraction of sequences `σ : Fin N → V` that contain a vertex of `A`. -/
theorem lemma_7_1 {V : Type*} [Fintype V] [DecidableEq V] (k : ℝ) (hk : 1 ≤ k)
    (A : Finset V) (hA : k ≤ (A.card : ℝ)) :
    ((Finset.univ.filter (fun σ : Fin ⌈10 * ((Fintype.card V : ℝ) / k) *
          Real.logb 2 (Fintype.card V)⌉₊ → V => ∃ j, σ j ∈ A)).card : ℝ) /
        (Fintype.card (Fin ⌈10 * ((Fintype.card V : ℝ) / k) *
          Real.logb 2 (Fintype.card V)⌉₊ → V) : ℝ) ≥
      1 - (Fintype.card V : ℝ) ^ (-10 : ℝ) := by sorry

end IncApproxVC.Oblivious
