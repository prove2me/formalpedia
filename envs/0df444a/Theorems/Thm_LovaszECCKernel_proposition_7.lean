-- Prove2me | Theorems.Thm_LovaszECCKernel_proposition_7
-- name    : LovaszECCKernel.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:22.567683+00:00
-- url     : https://prove2.me/theorems/f4addead-dbe0-4d96-b375-4ae442b23b28
-- title:
--   Proposition 7 — cocktail-party graphs with universal vertices: $\mathrm{ecc}\le\lceil\log_2n+\log_2\log_2n\rceil+2$
-- statement:
--   **Proposition 7.** Let $n\ge4$ and $u\ge0$, and let $G$ be the cocktail-party graph on $2n$ vertices (the complement of a perfect matching) with $u$ universal vertices added. Then
--   $$\mathrm{ecc}(G)\ \le\ \bigl\lceil\log_2n+\log_2\log_2n\bigr\rceil+2 .$$
--
--   Between two cliques of a deletion sequence of a complete multipartite graph the Lovász cover spends about $n$ Type-B cliques on such a graph; this logarithmic cover is the source of the savings in Lemmas 5 and 6.
--
--   Differences from the source:
--   - encoding: a cocktail-party graph with 2n vertices with an arbitrary number of universal vertices added → the graph cocktailParty n u on (Fin n × Bool) ⊕ Fin u, for every u; reason: every such graph is isomorphic to cocktailParty n u, and ecc is invariant under isomorphism
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Proposition 7, p.34 (= PDF p.34)

import Mathlib
import Definitions.Def_LovaszECCKernel_ecc
import Definitions.Def_LovaszECCKernel_cocktailParty

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Proposition 7** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Proposition 7, p.34 (= PDF p.34)): "Let G be a cocktail-party graph with
2n vertices, n ≥ 4, with an arbitrary number of universal vertices added above. Then
ecc(G) ≤ ⌈log2 n + log2 log2 n⌉ + 2."

**Formalization Note** `cocktailParty n u` is the complement of a perfect matching on `2n` vertices
with `u` universal vertices added, for every `u ≥ 0`. Logarithms are `Real.logb 2`; the ceiling is
`⌈·⌉₊` (its argument is at least `3` for `n ≥ 4`). -/
theorem proposition_7 (n u : ℕ) (hn : 4 ≤ n) :
    ecc (cocktailParty n u) ≤
      ⌈Real.logb 2 n + Real.logb 2 (Real.logb 2 n)⌉₊ + 2 := by sorry

end LovaszECCKernel
