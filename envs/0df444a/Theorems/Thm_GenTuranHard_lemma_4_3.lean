-- Prove2me | Theorems.Thm_GenTuranHard_lemma_4_3
-- name    : GenTuranHard.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:19.160732+00:00
-- url     : https://prove2.me/theorems/d744a84e-d1b1-4053-9f2b-72aa5338c6d5
-- title:
--   Lemma 4.3 — $\hom(T, L_{\mathbf x}(G)) = \sum_{(I_1,\dots,I_s)} \prod_i x_i^{|I_i|} \hom(T_s, G)$
-- statement:
--   For any graph $G$, bipartite graph $T$ and vector $\mathbf x = (x_1, \dots, x_s) \in \mathbb Z_{>0}^s$,
--
--   $$
--   \hom(T, L_{\mathbf x}(G)) = \sum_{(I_1, \dots, I_s) \text{ satisfying (4.1)}} \Big(\prod_{i=1}^{s} x_i^{|I_i|}\Big) \hom(T_s, G).
--   $$
--
--   This writes the number of homomorphisms into the leaf construction as a polynomial in $x_1, \dots, x_s$ whose coefficients are homomorphism counts of quotients of $T$ into $G$.
--
--   **Formalization Note** The length $s$ of $\mathbf x$ is arbitrary; the paper uses $s = v(T) - 2$.
--
--   Differences from the source:
--   - generalization: s = v(T) − 2 (the paper's s, p.14) → every length s of x; reason: the proof iterates Lemma 4.1 s times for any s; the paper's s is one case
--   - encoding: the vertices of Q_I (classes of V(Q)∖I and new isolated vertices v′) → quotGraph Q I renumbered on Fin v(Q_I) by a fixed bijection; reason: homomorphism counts, vertex counts, p(·), edges and bipartiteness do not depend on the numbering
--   - encoding: L_x(G) = L_{x₁}(L_{x₂}(⋯ L_{x_s}(G)⋯)) → iterLeaf x G = x.foldr leafAdd G, each leafAdd on Fin (m + m·x_i); reason: one numbering of the vertex set; homomorphism counts do not depend on it
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 4.3, p.14

import Mathlib
import Definitions.Def_GenTuranHard_leafAdd
import Definitions.Def_GenTuranHard_validSeqs

set_option autoImplicit false

namespace GenTuranHard

/-- **Lemma 4.3** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Lemma 4.3, p.14). For any
graph `G`, bipartite graph `T` and vector `x = (x₁, …, x_s)` of positive integers,
`hom(T, L_x(G)) = Σ_{(I₁,…,I_s) satisfying (4.1)} (∏_{i=1}^s x_i^{|I_i|}) hom(T_s, G)`.

**Formalization Note** `x` is a list of positive integers of any length `s` (the paper's
`s = v(T) − 2` is one case). `L_x(G)` is `iterLeaf x G`; the sequences of (4.1) start at `T`
renumbered on `Fin v(T)` (`toFin`), and `T_s` is `termGraph`. -/
theorem lemma_4_3 {W : Type} [Fintype W] (T : SimpleGraph W) (hT : T.IsBipartite) (G : FinGraph)
    (x : List ℕ) (hx : ∀ xi ∈ x, 0 < xi) :
    homCount T (iterLeaf x G).2 =
      ∑ Is ∈ validSeqs x.length (toFin T),
        monoWeight x Is * homCount (termGraph (toFin T) Is).2 G.2 := by sorry

end GenTuranHard
