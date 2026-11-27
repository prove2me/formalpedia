-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_5_1_fragment_size
-- name    : MetricTSPSublinear.lemma_5_1_fragment_size
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:05:26.665781+00:00
-- url     : https://prove2.me/theorems/50a4dcc4-3e81-4372-84b6-11a083d56e33
-- title:
--   Lemma 5.1(2): fragments are small with high probability
-- statement:
--   Let $F_{\mathrm{root}}$ be a rooted forest on $V=\{0,\dots,n-1\}$, given by a parent map with roots $R$ (and a rank that decreases along parent edges, so every vertex reaches a root). Draw $s$ vertices $S_{\mathrm{split}}$ independently and uniformly, let $F_{\mathrm{split}}$ consist of the roots and the paths from the sampled vertices to their roots, and let the fragments be the connected pieces of $F_{\mathrm{root}}$ outside $F_{\mathrm{split}}$. Then, counting over the $n^s$ sample tuples,
--   $$\#\{\text{tuples producing a fragment with at least }k\text{ vertices}\}\ \le\ n\cdot n^s\cdot e^{-ks/n}.$$
--   Equivalently, every fragment has fewer than $k$ vertices except with probability at most $n\,e^{-ks/n}$; with $s=n^{1-a_0}$ samples this gives fragments of size $\tilde O(n^{a_0})$ with high probability (Lemma 5.1(2)).
--
--   The proof shows that each fragment is the subtree of its top vertex and contains no sampled vertex, so a large fragment would be a large subtree missed by the sample.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, Lemma 5.1(2), p.15 (PDF p.17), and §9.1 'Constructing Ssplit', p.35 (PDF p.37).

import Mathlib
import Definitions.Def_MetricTSPSublinear_fragments

open Classical

namespace MetricTSPSublinear

open Fragments

/-- **Lemma 5.1, fragment sizes.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*,
arXiv:2611.04283, Lemma 5.1(2), p.15, with the argument of §9.1 "Constructing Ssplit", p.35: "for each vertex v
consider the subtree rooted at v in Froot. If this subtree contains Ω̃(n^{a0}) vertices, then with high probability it
includes a vertex sampled in Ssplit, and hence the subtree of v will be fragmented."

For a rooted forest (parent map `par`, roots `R`, a rank decreasing along parents) and `s` uniform samples, at most
`n · n^s · e^{−ks/n}` of the `n^s` sample tuples produce a fragment with at least `k` vertices. -/
theorem lemma_5_1_fragment_size {n : ℕ} (par : Fin n → Fin n) (rank : Fin n → ℕ) (R : Finset (Fin n))
    (hR : ∀ r ∈ R, par r = r) (hrank : ∀ v, v ∉ R → rank (par v) < rank v) (s k : ℕ) :
    ((Finset.univ.filter (fun σ : Fin s → Fin n => ∃ u, u ∉ Fsplit par R (Finset.univ.image σ) ∧
        k ≤ (frag par (Fsplit par R (Finset.univ.image σ)) u).card)).card : ℝ) ≤
      (n : ℝ) * ((n : ℝ) ^ s * Real.exp (-(k : ℝ) * s / n)) := by sorry

end MetricTSPSublinear
