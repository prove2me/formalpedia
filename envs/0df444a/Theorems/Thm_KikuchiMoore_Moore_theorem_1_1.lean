-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_theorem_1_1
-- name    : KikuchiMoore.Moore.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:42:13.370186+00:00
-- url     : https://prove2.me/theorems/c25e5001-7a0f-4c9e-9472-ed8e2c530ad2
-- title:
--   Theorem 1.1 — Hypergraph Moore bound with absolute constants
-- statement:
--   There exist positive absolute constants $A,C$ such that, for every integer $k\ge3$, every $1\le\ell\le n$, and every simple $k$-uniform hypergraph $H$ on the full ambient set $[n]$, at least one of
--
--   $$g_{\rm ev}(H)\le A\ell\log(en/\ell),\qquad |H|\le C\frac{n^{k/2}}{\ell^{k/2-1}}$$
--
--   holds. An even cover is a nonempty subfamily of distinct edges with even incidence at every vertex, and $g_{\rm ev}(H)=+\infty$ when none exists. The constants precede and are independent of $n,k,\ell,H$. Both parities, all levels, isolated vertices, and empty hypergraphs are included. This is the complete hypergraph Moore bound in Theorem 1.1.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: even girth at most a finite bound, with infinity for no even cover → existence of a nonempty finite subfamily with even incidence at every vertex and cardinality at most the bound; reason: equivalent for every finite bound, including hypergraphs without an even cover
--   - encoding: n^(k/2) / l^(k/2-1) and l log(en/l) → Real.rpow with real k/2 and Real.log (Real.exp 1 * n / l); reason: odd arity keeps its half-integer exponent and all stated domains have positive logarithm arguments
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Theorem 1.1, printed p. 3 = PDF p. 3, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Core

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem theorem_1_1  :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ (n k l : ℕ) (H : Hypergraph n),
      3 ≤ k → 1 ≤ l → l ≤ n → Uniform H k →
      HasCoverLE H (A * coverScale n l) ∨
      ((edges H).card : ℝ) ≤ C * densityScale n k l := by sorry

end KikuchiMoore.Moore
