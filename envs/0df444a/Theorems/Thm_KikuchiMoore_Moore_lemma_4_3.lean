-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_4_3
-- name    : KikuchiMoore.Moore.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:43:01.611652+00:00
-- url     : https://prove2.me/theorems/ed79b1ca-5d51-4138-8f5f-ae746b814e60
-- title:
--   Lemma 4.3 — Sparse remainder of maximal bundle packing
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Let $k\ge3$ and $1\le\ell\le n$. Choose a maximal edge-disjoint spread-bundle packing simultaneously over all residual sizes, with $m_+$ packed edges and $m_q$ packed at residual size $q$. If $m_0$ is the number of unabsorbed edges, then
--
--   $$m_0\le\frac2k\frac{n^{k/2}}{\ell^{k/2-1}}.$$
--
--   There is no parity or central-range restriction.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: a maximal edge-disjoint collection of spread bundles and its packed/remainder counts → inclusion-maximal finite sets of center/member bundles; packed counts are cardinalities of finite unions; reason: maximality is simultaneous over every residual size and disjointness makes these counts identical
--   - encoding: n^(k/2) / l^(k/2-1) and l log(en/l) → Real.rpow with real k/2 and Real.log (Real.exp 1 * n / l); reason: odd arity keeps its half-integer exponent and all stated domains have positive logarithm arguments
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 4.3, printed p. 16 = PDF p. 16, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Bundles

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_4_3 {n k l : ℕ} (H : Hypergraph n) (hk : 3 ≤ k)
    (hl : 1 ≤ l) (hln : l ≤ n) (hH : Uniform H k)
    (P : Finset (Bundle n)) (hP : MaximalPacking H k l P) :
    (remainder H P : ℝ) ≤ (2 / (k : ℝ)) * densityScale n k l := by sorry

end KikuchiMoore.Moore
