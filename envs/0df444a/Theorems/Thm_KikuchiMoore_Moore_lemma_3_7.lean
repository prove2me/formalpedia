-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_3_7
-- name    : KikuchiMoore.Moore.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:42:42.649995+00:00
-- url     : https://prove2.me/theorems/bd98f23d-1cf9-447f-aa0a-b2b7294db65b
-- title:
--   Lemma 3.7 — Sharp orientation and normalized norm
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Suppose $k=2r\ge4$ and $2k\le\ell$, $n\ge100k\ell$. Write $N=\binom n\ell$, $s=\lceil(3\ell/k)\log(en/\ell)\rceil$, and let $G,K,L$ be the concrete even Kikuchi graph, degree-plus-mean normalized matrix, and truncated parity lift. All norms are induced Euclidean norms and $\bar d$ is the realized mean degree of $G$. Assume $H\ne\varnothing$ and no even cover has size at most $\max(2s,\ell+ks+1)$. Every retained lifted state has incoming degree at most $2\ell$ under the specified window orientation, and
--
--   $$\|K\|\le2\sqrt{2\ell/\bar d}\,N^{1/(2s)}.$$
--
--   Equal-window edges point toward the row containing their fixed label representative; unequal-window edges point toward the larger window. Both conclusions are required.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: even k = 2r at least 4 → r is a natural number at least 2 and k is substituted by 2*r; reason: this parametrizes every permitted even arity
--   - encoding: even girth at most a finite bound, with infinity for no even cover → existence of a nonempty finite subfamily with even incidence at every vertex and cardinality at most the bound; reason: equivalent for every finite bound, including hypergraphs without an even cover
--   - encoding: fix a representative system on each window → choose one such system when it exists; reason: classical choice fixes the source-permitted arbitrary systems; no representative or degree bound is assumed
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 3.7, printed p. 15 = PDF p. 15, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Even

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_3_7 {n l r : ℕ} (H : Hypergraph n) (hr : 2 ≤ r)
    (hH : Uniform H (2*r)) (hc : Central n (2*r) l) (hne : (edges H).Nonempty)
    (hcover : ¬ HasCoverLE H
      (max (2 * evenLength n (2*r) l) (l + 2*r*evenLength n (2*r) l + 1) : ℕ)) :
    (∀ x : State n l, evenReachable H r (evenLength n (2*r) l) x →
      evenIncoming H r (evenLength n (2*r) l) x ≤ 2*l) ∧
    opNorm (normalized (evenAdj (l := l) H r)) ≤
      2 * Real.sqrt (2 * (l : ℝ) / meanDegree (evenAdj (l := l) H r)) *
        Real.rpow (Nat.choose n l : ℝ) (1 / (2 * (evenLength n (2*r) l : ℝ))) := by sorry

end KikuchiMoore.Moore
