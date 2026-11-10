-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_proposition_4_7
-- name    : KikuchiMoore.Moore.proposition_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:44:00.458439+00:00
-- url     : https://prove2.me/theorems/18ddd3b1-3933-4276-ba52-727fa79e0e76
-- title:
--   Proposition 4.7 — Paired trace estimate without a central-range restriction
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Let $k\ge3$, $1\le\ell\le n$, and $s\ge1$. Choose a maximal edge-disjoint spread-bundle packing simultaneously over all residual sizes, with $m_+$ packed edges and $m_q$ packed at residual size $q$. Choose any $1\le q\le k-1$ and form the exact weighted balanced paired graph $Y$ at this size. If no even cover has size at most $\max(4s,2\ell+4ks+2)$, then
--
--   $$\bar d\le32\ell\binom n\ell^{1/s}.$$
--
--   The mean is realized, and zero degree is allowed. Neither parity nor the central range is assumed.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: a maximal edge-disjoint collection of spread bundles and its packed/remainder counts → inclusion-maximal finite sets of center/member bundles; packed counts are cardinalities of finite unions; reason: maximality is simultaneous over every residual size and disjointness makes these counts identical
--   - encoding: undirected labeled transition instances and four-port contention weights → a pair of two-element finite sets stores the endpoint rows and labels; weights use real c(z)-1; reason: each undirected instance appears once, parallel label pairs survive, and every actual port has contention at least one
--   - encoding: even girth at most a finite bound, with infinity for no even cover → existence of a nonempty finite subfamily with even incidence at every vertex and cardinality at most the bound; reason: equivalent for every finite bound, including hypergraphs without an even cover
--   - generalization: Y at the fixed dominant residual size when packed edges are nonempty → Y at any allowed residual size, including an empty selected family; reason: the paired trace and port-capacity argument uses no dominance; the dominant source choice is included and zero degree satisfies the bound
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Proposition 4.7, printed p. 19 = PDF p. 19, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Paired

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem proposition_4_7 {n k l q s : ℕ} (H : Hypergraph n) (hk : 3 ≤ k)
    (hl : 1 ≤ l) (hln : l ≤ n) (hH : Uniform H k)
    (P : Finset (Bundle n)) (hP : MaximalPacking H k l P)
    (hq : 1 ≤ q ∧ q ≤ k-1) (hs : 1 ≤ s)
    (hcover : ¬ HasCoverLE H (max (4*s) (2*l+4*k*s+2) : ℕ)) :
    meanDegree (pairedAdj (l := l) k q P) ≤
      32 * (l : ℝ) * Real.rpow (Nat.choose n l : ℝ) (1 / (s : ℝ)) := by sorry

end KikuchiMoore.Moore
