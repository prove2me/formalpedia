-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_theorem_3_1
-- name    : KikuchiMoore.Moore.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:41:50.607646+00:00
-- url     : https://prove2.me/theorems/bab01048-a803-4cbd-9928-1849f2285be4
-- title:
--   Theorem 3.1 — Even central-range Moore bound
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Suppose $k=2r\ge4$ and $2k\le\ell$, $n\ge100k\ell$. Write $N=\binom n\ell$, $s=\lceil(3\ell/k)\log(en/\ell)\rceil$, and let $G,K,L$ be the concrete even Kikuchi graph, degree-plus-mean normalized matrix, and truncated parity lift. All norms are induced Euclidean norms and $\bar d$ is the realized mean degree of $G$. If no even cover has size at most $5\ell\log(en/\ell)$, then
--
--   $$|H|\le45\,\frac{n^{k/2}}{\ell^{k/2-1}}.$$
--
--   The constants are exactly 5 and 45, and $H$ may be empty.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: even k = 2r at least 4 → r is a natural number at least 2 and k is substituted by 2*r; reason: this parametrizes every permitted even arity
--   - encoding: even girth at most a finite bound, with infinity for no even cover → existence of a nonempty finite subfamily with even incidence at every vertex and cardinality at most the bound; reason: equivalent for every finite bound, including hypergraphs without an even cover
--   - encoding: n^(k/2) / l^(k/2-1) and l log(en/l) → Real.rpow with real k/2 and Real.log (Real.exp 1 * n / l); reason: odd arity keeps its half-integer exponent and all stated domains have positive logarithm arguments
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Theorem 3.1, printed p. 13 = PDF p. 13, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Core

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem theorem_3_1 {n l r : ℕ} (H : Hypergraph n) (hr : 2 ≤ r)
    (hH : Uniform H (2*r)) (hc : Central n (2*r) l)
    (hcover : ¬ HasCoverLE H (5 * coverScale n l)) :
    ((edges H).card : ℝ) ≤ 45 * densityScale n (2*r) l := by sorry

end KikuchiMoore.Moore
