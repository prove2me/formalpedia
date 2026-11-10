-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_3_3
-- name    : KikuchiMoore.Moore.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:42:47.063774+00:00
-- url     : https://prove2.me/theorems/56b80af8-c1cb-4da2-a83d-3fd42a0cd731
-- title:
--   Lemma 3.3 — Even hyperedges give sufficient degree
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Suppose $k=2r\ge4$ and $2k\le\ell$, $n\ge100k\ell$. Write $N=\binom n\ell$, $s=\lceil(3\ell/k)\log(en/\ell)\rceil$, and let $G,K,L$ be the concrete even Kikuchi graph, degree-plus-mean normalized matrix, and truncated parity lift. All norms are induced Euclidean norms and $\bar d$ is the realized mean degree of $G$. Then
--
--   $$\bar d\ge\frac9{20\sqrt r}\left(\frac8e\right)^r\left(\frac\ell n\right)^r|H|.$$
--
--   The empty hypergraph is included.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: even k = 2r at least 4 → r is a natural number at least 2 and k is substituted by 2*r; reason: this parametrizes every permitted even arity
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 3.3, printed p. 14 = PDF p. 14, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Even

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_3_3 {n l r : ℕ} (H : Hypergraph n) (hr : 2 ≤ r)
    (hH : Uniform H (2*r)) (hc : Central n (2*r) l) :
    9 / (20 * Real.sqrt (r : ℝ)) * (8 / Real.exp 1)^r * ((l : ℝ)/n)^r *
      (edges H).card ≤ meanDegree (evenAdj (l := l) H r) := by sorry

end KikuchiMoore.Moore
