-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_3_6
-- name    : KikuchiMoore.Moore.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:42:36.456891+00:00
-- url     : https://prove2.me/theorems/b6cece87-7469-4364-9c77-cd78c7920dd5
-- title:
--   Lemma 3.6 — Distinct representatives in every small window
-- statement:
--   Let $H$ be a simple $k$-uniform hypergraph on the full ambient vertex set $[n]$, possibly empty and with isolated vertices. Suppose $k=2r\ge4$ and $2k\le\ell$, $n\ge100k\ell$. Write $N=\binom n\ell$, $s=\lceil(3\ell/k)\log(en/\ell)\rceil$, and let $G,K,L$ be the concrete even Kikuchi graph, degree-plus-mean normalized matrix, and truncated parity lift. All norms are induced Euclidean norms and $\bar d$ is the realized mean degree of $G$. If no even cover has size at most $\ell+ks+1$, then every $W\subseteq[n]$ with $|W|\le\ell+ks$ admits an injective map
--
--   $$\rho_W:H[W]\to W,\qquad \rho_W(F)\in F,$$
--
--   where $H[W]=\{F\in H:F\subseteq W\}$.
--
--   Differences from the source:
--   - encoding: simple uniform hypergraphs on [n] → the published FinHypergraph on Fin n with declared vertex set equal to the full ambient set; reason: zero-based indexing is a bijective relabeling; set-valued edges retain distinctness and isolated vertices
--   - encoding: even k = 2r at least 4 → r is a natural number at least 2 and k is substituted by 2*r; reason: this parametrizes every permitted even arity
--   - encoding: even girth at most a finite bound, with infinity for no even cover → existence of a nonempty finite subfamily with even incidence at every vertex and cardinality at most the bound; reason: equivalent for every finite bound, including hypergraphs without an even cover
--   - generalization: the surrounding normalization discussion assumes H is nonempty → the representative conclusion also allows H empty; reason: the injection from the empty edge family exists, so this adds instances without losing any source instance
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 3.6, printed p. 15 = PDF p. 15, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Even

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_3_6 {n l r : ℕ} (H : Hypergraph n) (hr : 2 ≤ r)
    (hH : Uniform H (2*r)) (hc : Central n (2*r) l)
    (hcover : ¬ HasCoverLE H (l + 2*r*evenLength n (2*r) l + 1)) :
    ∀ W : Finset (Fin n), W.card ≤ l + 2*r*evenLength n (2*r) l →
      ∃ rho : {F // F ∈ inducedEdges H W} → {v // v ∈ W},
        Function.Injective rho ∧ ∀ F, (rho F).val ∈ F.val := by sorry

end KikuchiMoore.Moore
