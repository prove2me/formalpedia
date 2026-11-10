-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_4_6
-- name    : KikuchiMoore.Moore.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:43:39.107195+00:00
-- url     : https://prove2.me/theorems/9bf34b26-dfa2-4e50-8c96-4898a760d6ae
-- title:
--   Lemma 4.6 — Weighted degree lower bound
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Suppose $k=2r+1\ge3$, $2k\le\ell$, and $n\ge100k\ell$. Choose a maximal edge-disjoint spread-bundle packing simultaneously over all residual sizes, with $m_+$ packed edges and $m_q$ packed at residual size $q$. Assume $m_+>0$ and choose $1\le q\le k-1$ with $m_q\ge m_+/(k-1)$. Use every balanced residual-disjoint paired transition at size $q$, retaining parallel label pairs; $c(z)$ is its four-port contention, $\mu_q$ its number of instances, and $Y$ its exact weighted graph with weights $[1+\sum_{z\in P(e)}(c(z)-1)]^{-1}$. For the realized weighted average degree $\bar d=N^{-1}\sum_S d(S)=2N^{-1}\sum_e w_e$,
--
--   $$\bar d\ge\frac{(1.0324)^k}{74k^3}m_+(\ell/n)^{k/2}.$$
--
--   All constants are exact.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: odd k = 2r+1 at least 3 → r is a natural number at least 1 and k is substituted by 2*r+1; reason: this parametrizes every permitted odd arity
--   - encoding: a maximal edge-disjoint collection of spread bundles and its packed/remainder counts → inclusion-maximal finite sets of center/member bundles; packed counts are cardinalities of finite unions; reason: maximality is simultaneous over every residual size and disjointness makes these counts identical
--   - encoding: undirected labeled transition instances and four-port contention weights → a pair of two-element finite sets stores the endpoint rows and labels; weights use real c(z)-1; reason: each undirected instance appears once, parallel label pairs survive, and every actual port has contention at least one
--   - encoding: 1.0324 and k/2 → the exact rational 2581/2500 and real half-integer division; reason: preserves the printed constant and odd-arity scale
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 4.6, printed p. 19 = PDF p. 19, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Paired

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_4_6 {n l r q : ℕ} (H : Hypergraph n) (hr : 1 ≤ r)
    (hH : Uniform H (2*r+1)) (hc : Central n (2*r+1) l)
    (P : Finset (Bundle n)) (hP : MaximalPacking H (2*r+1) l P)
    (hq : Dominant (2*r+1) q P) :
    (1.0324 : ℝ)^(2*r+1) / (74 * (2*(r : ℝ)+1)^3) * (packed P).card *
      Real.rpow ((l : ℝ)/n) ((2*(r : ℝ)+1)/2) ≤
    meanDegree (pairedAdj (l := l) (2*r+1) q P) := by sorry

end KikuchiMoore.Moore
