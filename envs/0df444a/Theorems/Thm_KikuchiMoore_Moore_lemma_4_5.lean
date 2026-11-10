-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_4_5
-- name    : KikuchiMoore.Moore.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:44:01.285599+00:00
-- url     : https://prove2.me/theorems/d7cae63d-bb2e-4d63-8f42-a9ac6db113db
-- title:
--   Lemma 4.5 — Exact excess-contention estimate
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Suppose $k=2r+1\ge3$, $2k\le\ell$, and $n\ge100k\ell$. Choose a maximal edge-disjoint spread-bundle packing simultaneously over all residual sizes, with $m_+$ packed edges and $m_q$ packed at residual size $q$. Assume $m_+>0$ and choose $1\le q\le k-1$ with $m_q\ge m_+/(k-1)$. Use every balanced residual-disjoint paired transition at size $q$, retaining parallel label pairs; $c(z)$ is its four-port contention, $\mu_q$ its number of instances, and $Y$ its exact weighted graph with weights $[1+\sum_{z\in P(e)}(c(z)-1)]^{-1}$. Put $a=\lfloor q/2\rfloor$, $b=\lceil q/2\rceil$, and $B_q=\binom qa$. Both assertions hold:
--
--   1. If $q\le r$, every port has $c(z)\le1$.
--   2. If $q\ge r+1$,
--
--   $$\sum_z c(z)(c(z)-1)\le\Xi_q\mu_q,\qquad \Xi_q=8B_q(2.031)^a(n/\ell)^{b-k/2}.$$
--
--   The decimal constant and the negative half-integer exponent are retained.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: odd k = 2r+1 at least 3 → r is a natural number at least 1 and k is substituted by 2*r+1; reason: this parametrizes every permitted odd arity
--   - encoding: a maximal edge-disjoint collection of spread bundles and its packed/remainder counts → inclusion-maximal finite sets of center/member bundles; packed counts are cardinalities of finite unions; reason: maximality is simultaneous over every residual size and disjointness makes these counts identical
--   - encoding: undirected labeled transition instances and four-port contention weights → a pair of two-element finite sets stores the endpoint rows and labels; weights use real c(z)-1; reason: each undirected instance appears once, parallel label pairs survive, and every actual port has contention at least one
--   - encoding: the decimal 2.031 and exponent b-k/2 → the exact rational 2031/1000 and a real exponent with b computed by natural ceiling division; reason: no numerical rounding or integer truncation of k/2 occurs
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 4.5, printed p. 18 = PDF p. 18, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Paired

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_4_5 {n l r q : ℕ} (H : Hypergraph n) (hr : 1 ≤ r)
    (hH : Uniform H (2*r+1)) (hc : Central n (2*r+1) l)
    (P : Finset (Bundle n)) (hP : MaximalPacking H (2*r+1) l P)
    (hq : Dominant (2*r+1) q P) :
    (q ≤ r → ∀ z : Port n l, contention (pairInstances (2*r+1) q P) z ≤ 1) ∧
    (r+1 ≤ q → excess (pairInstances (l := l) (2*r+1) q P) ≤
      xi n (2*r+1) l q * (pairInstances (l := l) (2*r+1) q P).card) := by sorry

end KikuchiMoore.Moore
