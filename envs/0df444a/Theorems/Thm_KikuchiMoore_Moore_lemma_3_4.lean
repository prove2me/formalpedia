-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_3_4
-- name    : KikuchiMoore.Moore.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:42:55.685519+00:00
-- url     : https://prove2.me/theorems/3f5f9247-2779-478e-a669-5df9da6dec1f
-- title:
--   Lemma 3.4 — Trace equality for the parity lift
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Suppose $k=2r\ge4$ and $2k\le\ell$, $n\ge100k\ell$. Write $N=\binom n\ell$, $s=\lceil(3\ell/k)\log(en/\ell)\rceil$, and let $G,K,L$ be the concrete even Kikuchi graph, degree-plus-mean normalized matrix, and truncated parity lift. All norms are induced Euclidean norms and $\bar d$ is the realized mean degree of $G$. Assume $H\ne\varnothing$ and no even cover has size at most $2s$. Then
--
--   $$\operatorname{Tr}K^{2s}=\sum_{S\in\Omega_\ell}(L^{2s})_{(S,\varnothing),(S,\varnothing)}.$$
--
--   The trace is unnormalized.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: even k = 2r at least 4 → r is a natural number at least 2 and k is substituted by 2*r; reason: this parametrizes every permitted even arity
--   - encoding: even girth at most a finite bound, with infinity for no even cover → existence of a nonempty finite subfamily with even incidence at every vertex and cardinality at most the bound; reason: equivalent for every finite bound, including hypergraphs without an even cover
--   - encoding: the lift restricted to components containing an empty-memory state → the same weighted matrix extended by zero to excluded states; reason: zero padding preserves Euclidean operator norm and all empty-memory diagonal matrix-power entries
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 3.4, printed p. 14 = PDF p. 14, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Even

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_3_4 {n l r : ℕ} (H : Hypergraph n) (hr : 2 ≤ r)
    (hH : Uniform H (2*r)) (hc : Central n (2*r) l) (hne : (edges H).Nonempty)
    (hcover : ¬ HasCoverLE H (2 * evenLength n (2*r) l)) :
    Matrix.trace ((normalized (evenAdj (l := l) H r)) ^ (2 * evenLength n (2*r) l)) =
      ∑ S : Row n l, ((evenLift H r (evenLength n (2*r) l)) ^
        (2 * evenLength n (2*r) l)) (S, ∅) (S, ∅) := by sorry

end KikuchiMoore.Moore
