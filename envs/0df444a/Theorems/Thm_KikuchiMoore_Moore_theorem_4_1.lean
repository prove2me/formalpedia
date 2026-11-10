-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_theorem_4_1
-- name    : KikuchiMoore.Moore.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:41:54.994677+00:00
-- url     : https://prove2.me/theorems/fb2b8607-2b3d-417f-962d-6ad813c4c2cb
-- title:
--   Theorem 4.1 — Odd central-range Moore bound
-- statement:
--   There are positive absolute constants $A,C$, chosen before all dimensions, levels, arities, and hypergraphs, such that the following holds. Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Suppose $k=2r+1\ge3$, $2k\le\ell$, and $n\ge100k\ell$. If no even cover has size at most $A\ell\log(en/\ell)$, then
--
--   $$|H|\le C\frac{n^{k/2}}{\ell^{k/2-1}}.$$
--
--   The constants are uniform even when $k$ varies; the source statement is existential rather than the proof's particular choice $A=165$.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: odd k = 2r+1 at least 3 → r is a natural number at least 1 and k is substituted by 2*r+1; reason: this parametrizes every permitted odd arity
--   - encoding: even girth at most a finite bound, with infinity for no even cover → existence of a nonempty finite subfamily with even incidence at every vertex and cardinality at most the bound; reason: equivalent for every finite bound, including hypergraphs without an even cover
--   - encoding: n^(k/2) / l^(k/2-1) and l log(en/l) → Real.rpow with real k/2 and Real.log (Real.exp 1 * n / l); reason: odd arity keeps its half-integer exponent and all stated domains have positive logarithm arguments
--   - reading: absolute constants A and C → constants A > 0 and C > 0; reason: the paper's absolute constants are positive (A = 165 in the proof, and Theorem 1.1 states A, C > 0); a nonpositive cover radius or density constant is not what the statement means
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Theorem 4.1, printed p. 16 = PDF p. 16, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Core

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem theorem_4_1  :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ (n l r : ℕ) (H : Hypergraph n),
      1 ≤ r → Uniform H (2*r+1) → Central n (2*r+1) l →
      ¬ HasCoverLE H (A * coverScale n l) →
      ((edges H).card : ℝ) ≤ C * densityScale n (2*r+1) l := by sorry

end KikuchiMoore.Moore
