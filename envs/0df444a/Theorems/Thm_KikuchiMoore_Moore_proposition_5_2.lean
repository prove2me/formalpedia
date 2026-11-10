-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_proposition_5_2
-- name    : KikuchiMoore.Moore.proposition_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:41:58.503213+00:00
-- url     : https://prove2.me/theorems/4bf41fb7-46d7-4639-80ae-74112991a1b3
-- title:
--   Proposition 5.2 — Crossed halves for very small levels
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Suppose $k\ge3$, $1\le\ell\le n$, and $k>400\ell$, with either parity. At least one of
--
--   $$g_{\rm ev}(H)\le22\ell\log(en/\ell),\qquad |H|\le50\frac{n^{k/2}}{\ell^{k/2-1}}$$
--
--   holds. There is no additional restriction $k\le n$; the empty hypergraph case is retained.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: even girth at most a finite bound, with infinity for no even cover → existence of a nonempty finite subfamily with even incidence at every vertex and cardinality at most the bound; reason: equivalent for every finite bound, including hypergraphs without an even cover
--   - encoding: n^(k/2) / l^(k/2-1) and l log(en/l) → Real.rpow with real k/2 and Real.log (Real.exp 1 * n / l); reason: odd arity keeps its half-integer exponent and all stated domains have positive logarithm arguments
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Proposition 5.2, printed p. 21 = PDF p. 21, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Core

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem proposition_5_2 {n k l : ℕ} (H : Hypergraph n) (hk : 3 ≤ k)
    (hl : 1 ≤ l) (hln : l ≤ n) (hH : Uniform H k) (hsmall : 400*l < k) :
    HasCoverLE H (22 * coverScale n l) ∨
    ((edges H).card : ℝ) ≤ 50 * densityScale n k l := by sorry

end KikuchiMoore.Moore
