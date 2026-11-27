-- Prove2me | Theorems.Thm_MetricTSPSublinear_sample_hits_large_sets
-- name    : MetricTSPSublinear.sample_hits_large_sets
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:58:58.759231+00:00
-- url     : https://prove2.me/theorems/466599ff-b418-423d-ae64-5c47436a8a35
-- title:
--   Uniform samples hit every large set (union bound)
-- statement:
--   Let $A_j\subseteq\{0,\dots,K-1\}$, $j\in J$, be finitely many sets, each with at least $a$ elements, and draw $s$ indices independently and uniformly from $\{0,\dots,K-1\}$. Counting over all $K^s$ outcomes, the number of tuples that miss at least one of the sets is at most
--   $$|J|\cdot K^s\cdot e^{-as/K}.$$
--   Equivalently, the probability that the sample misses some $A_j$ is at most $|J|\,e^{-as/K}$.
--
--   In the paper this is the standard union bound behind the high-probability statements of Lemma 5.1 and Claim 9.2: a random sample of size $\tilde O(n^{1-a_0})$ meets every set of $\tilde\Omega(n^{a_0})$ vertices among a polynomial family, which bounds the fragment sizes and the length of the Prim explorations.
--
--   **Formalization Note** Probabilities are stated as counts over the $K^s$ sample tuples, matching the coin-tape model of the machine, where $s$ samples of $m$ coins give uniform tuples over $\{0,\dots,2^m-1\}$.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §9.1, proof of Lemma 5.1 and Claim 9.2, p.35 (PDF p.37).

import Mathlib

namespace MetricTSPSublinear

/-- **A uniform sample hits every large set (union bound).** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time:
Breaking Two Approximation*, arXiv:2611.04283, §9.1, p.35 (PDF p.37): "If this subtree contains Ω̃(n^{a0}) vertices,
then with high probability it includes a vertex sampled in Ssplit"; Claim 9.2, p.35: "there will be a vertex of Sroot
in the first Õ(n^{a0}) vertices of the ordering, with high probability". Among the `K^s` tuples of `s` uniform samples
from `Fin K`, at most `|J| · K^s · e^{−a s/K}` miss one of the sets `A j`, each of size at least `a`. -/
theorem sample_hits_large_sets {J : Type*} [Fintype J] (K s a : ℕ) (hK : 0 < K) (A : J → Finset (Fin K))
    (hA : ∀ j, a ≤ (A j).card) :
    ((Finset.univ.filter (fun u : Fin s → Fin K => ∃ j, ∀ i, u i ∉ A j)).card : ℝ) ≤
      (Fintype.card J : ℝ) * ((K : ℝ) ^ s * Real.exp (-(a : ℝ) * s / K)) := by sorry

end MetricTSPSublinear
