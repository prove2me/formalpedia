-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_5_1
-- name    : KikuchiMoore.Moore.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:41:51.998588+00:00
-- url     : https://prove2.me/theorems/736a8dd4-c0d8-4bdb-9e2d-bb4c48f11dd2
-- title:
--   Lemma 5.1 — Dense-regime syndrome bound
-- statement:
--   There is a positive absolute constant $C$ such that for every $k\ge3$, $1\le\ell\le n$, and simple $k$-uniform hypergraph $H$ on $[n]$, if $n\le100k\ell$, at least one of
--
--   $$g_{\rm ev}(H)\le C\ell\log(en/\ell),\qquad |H|\le C\frac{n^{k/2}}{\ell^{k/2-1}}$$
--
--   holds. The same $C$ occurs in both alternatives and is independent of every parameter. Even girth is infinite if no even cover exists.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: even girth at most a finite bound, with infinity for no even cover → existence of a nonempty finite subfamily with even incidence at every vertex and cardinality at most the bound; reason: equivalent for every finite bound, including hypergraphs without an even cover
--   - encoding: n^(k/2) / l^(k/2-1) and l log(en/l) → Real.rpow with real k/2 and Real.log (Real.exp 1 * n / l); reason: odd arity keeps its half-integer exponent and all stated domains have positive logarithm arguments
--   - reading: an absolute constant C → a constant C > 0; reason: C is the positive absolute constant of Theorem 1.1, into whose proof the lemma feeds (p. 22)
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 5.1, printed p. 21 = PDF p. 21, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Core

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_5_1  :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k l : ℕ) (H : Hypergraph n),
      3 ≤ k → 1 ≤ l → l ≤ n → Uniform H k → n ≤ 100*k*l →
      HasCoverLE H (C * coverScale n l) ∨
      ((edges H).card : ℝ) ≤ C * densityScale n k l := by sorry

end KikuchiMoore.Moore
