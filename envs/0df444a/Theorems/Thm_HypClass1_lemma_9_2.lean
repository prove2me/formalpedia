-- Prove2me | Theorems.Thm_HypClass1_lemma_9_2
-- name    : HypClass1.lemma_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:29:57.982633+00:00
-- url     : https://prove2.me/theorems/1013c0a7-a758-4065-9bf4-5c14a0b16c58
-- title:
--   Lemma 9.2 — edge-disjoint matchings through $x^\star$ leaving a sparse remainder
-- statement:
--   Let $\alpha \in (0,1)$ and let $p = p(n)$ satisfy $n^{-1+\alpha} \le p \le 0.99$. Let $H \sim H^{(3)}_{n,p}$ and let $x^\star$ be the vertex of maximum degree of $H$. Then with high probability $H$ contains a collection $\mathcal K$ of edge-disjoint matchings such that the remainder $R = H \setminus \bigcup_{K \in \mathcal K} K$ satisfies:
--   1. (K1) $\Delta(R) \le n^{1+\alpha}$ and $\Delta_2(R) \le n^{\alpha}$;
--   2. (K2) $x^\star \in V(K)$ for every $K \in \mathcal K$;
--   3. (K3) $\deg_R(x^\star) - \deg_R(y) \ge \sqrt{pn^2}/\log^2 n$ for every vertex $y \ne x^\star$.
--
--   This is the output of the iterative absorption procedure (Stages I and II applied alternately over $2t$ exposure rounds).
--
--   **Formalization Note** The event includes that $H$ has a unique vertex $x^\star$ of maximum degree. $\mathcal K$ is a finite set of pairwise edge-disjoint matchings contained in $H$.
--
--   Differences from the source:
--   - reading: p := p(n) with n^{−1+α} ≤ p ≤ 0.99 → the bounds hold for all sufficiently large n; reason: at n = 1 the bounds read 1 ≤ p ≤ 0.99; the statement is asymptotic
--   - reading: 'with high probability' (never defined in the paper) → probability → 1 as n → ∞ (Tendsto … atTop (𝓝 1)); reason: the standard meaning
--   - reading: 'x⋆ be the vertex of maximum degree in H' → the event asserts that H has a unique vertex x⋆ of maximum degree; reason: the definite article presupposes uniqueness; this is the stronger reading, and Theorem 9.1 makes it hold with high probability in this range
--   - encoding: a collection of edge disjoint matchings K → a Finset of pairwise edge-disjoint matchings, each contained in H; reason: by (K2) every matching is non-empty, and distinct non-empty edge-disjoint matchings cannot repeat, so no multiplicity is lost
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 9.2, pp.46–47

import Mathlib
import Definitions.Def_HypClass1_binomProb
import Definitions.Def_MatchVec3_maxDegree
import Definitions.Def_HypClass1_deg
import Definitions.Def_HypClass1_maxCodeg
import Definitions.Def_HypClass1_IsMatching

open Filter Topology

namespace HypClass1

/-- **Lemma 9.2 (iterative absorption).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 9.2, pp.46–47:
"Let α ∈ (0, 1) and p := p(n) be real numbers satisfying n^{−1+α} ≤ p ≤ 0.99. Let H ∼ H^{(3)}_{n,p} and
x⋆ be the vertex of maximum degree in H. Then, with high probability, the 3-graph H contains a
collection of edge disjoint matchings K and a remainder 3-graph R = H ∖ ⋃_{K∈K} K with the following
properties
(K1) The 3-graph R satisfies ∆(R) ≤ n^{1+α} and ∆₂(R) ≤ n^α.
(K2) For every K ∈ K, it holds that x⋆ ∈ V(K).
(K3) For every vertex y ≠ x⋆ it holds that deg_R(x⋆) − deg_R(y) ≥ √(pn²)/log² n."

**Formalization Note.** For every fixed `α ∈ (0, 1)` and every sequence `p(n)` with the bounds for
all large `n`; "with high probability" is `P → 1`. The event: `H` has a unique vertex `x⋆` of maximum
degree, and a finite set `𝒦` of pairwise edge-disjoint matchings, each contained in `H`, satisfies
(K1)–(K3) for `R = H ∖ ⋃𝒦`. -/
theorem lemma_9_2 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (p : ℕ → ℝ)
    (hp : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-1 + α) ≤ p n ∧ p n ≤ 0.99) :
    Tendsto (fun n : ℕ => binomProb n (p n) (fun H =>
        ∃ xs : Fin n, (∀ y : Fin n, y ≠ xs → deg H y < deg H xs) ∧
        ∃ 𝒦 : Finset (Finset (Finset (Fin n))),
          (∀ K ∈ 𝒦, K ⊆ H ∧ IsMatching K) ∧
          (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → Disjoint K K') ∧
          ((MatchVec3.maxDegree (H \ 𝒦.biUnion id) : ℝ) ≤ (n : ℝ) ^ (1 + α) ∧
            (maxCodeg (H \ 𝒦.biUnion id) : ℝ) ≤ (n : ℝ) ^ α) ∧
          (∀ K ∈ 𝒦, xs ∈ verts K) ∧
          (∀ y : Fin n, y ≠ xs →
            Real.sqrt (p n * (n : ℝ) ^ 2) / Real.log n ^ 2 ≤
              (deg (H \ 𝒦.biUnion id) xs : ℝ) - deg (H \ 𝒦.biUnion id) y)))
      atTop (𝓝 1) := by sorry

end HypClass1
