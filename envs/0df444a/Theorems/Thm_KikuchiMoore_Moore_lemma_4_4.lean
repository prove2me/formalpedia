-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_4_4
-- name    : KikuchiMoore.Moore.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:42:50.131533+00:00
-- url     : https://prove2.me/theorems/beff9854-a001-4b01-92cc-7a0650c53c19
-- title:
--   Lemma 4.4 — Many disjoint residual pairs in each bundle
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Suppose $k=2r+1\ge3$, $2k\le\ell$, and $n\ge100k\ell$. For any spread bundle $B$ of residual size $1\le q\le k-1$, the number of unordered pairs $\{F,J\}\subseteq B$ with $R_F\cap R_J=\varnothing$ is at least
--
--   $$h_q^2/4.$$
--
--   Here $h_q=\max(2,\lceil(n/\ell)^{q-k/2}\rceil)$ and the spread inequality is strict.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: odd k = 2r+1 at least 3 → r is a natural number at least 1 and k is substituted by 2*r+1; reason: this parametrizes every permitted odd arity
--   - encoding: unordered residual-disjoint pairs → two-element finite subfamilies satisfying pairwise residual disjointness; reason: counts each distinct unordered pair exactly once
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 4.4, printed p. 17 = PDF p. 17, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Bundles

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_4_4 {n l r q : ℕ} (H : Hypergraph n) (hr : 1 ≤ r)
    (hH : Uniform H (2*r+1)) (hc : Central n (2*r+1) l)
    (B : Bundle n) (hB : SpreadBundle H (2*r+1) l q B) :
    (bundleSize n (2*r+1) l q : ℝ)^2 / 4 ≤ (disjointPairs B).card := by sorry

end KikuchiMoore.Moore
