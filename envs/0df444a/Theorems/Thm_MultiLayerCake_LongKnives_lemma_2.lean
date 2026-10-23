-- Prove2me | Theorems.Thm_MultiLayerCake_LongKnives_lemma_2
-- name    : MultiLayerCake.LongKnives.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:39.683605+00:00
-- url     : https://prove2.me/theorems/ed3d86d7-aa64-4b73-b303-5eb7d051970a
-- title:
--   Lemma 2, p. 7 — the encoding is equivariant: A_j(x) = A_{g+j}(g·x)
-- statement:
--   Let $G$ be a finite additive group of order $q$, $\mathfrak P$ a procedure assigning to each support a $(q-1)$-simplex of the chessboard complex $\Delta_{2q-1,q}$ equivariantly, and $h:[m]\to G$ injective. For a point $x$ of $\|\Delta_{2q-1,q}\|$ let $\mathcal A(x)=(\mathcal A_j(x))_{j\in G}$ be the multi-division it encodes. Then for all $x\in\|\Delta_{2q-1,q}\|$, $j\in G$ and $g\in G$,
--   $$\mathcal A_j(x)=\mathcal A_{g+j}(g\cdot x),$$
--   where $g\cdot x$ is the action of $G$ on the chessboard, $g\cdot(r,j)=(r,g+j)$.
--
--   The identity says that relabelling the columns by $g$ relabels the bundles by $g$; it is what lets the agents' labellings in the proof of Theorem 1 be extended equivariantly from orbit representatives.
--
--   **Formalization Note.** The page's bijection $\eta:[q]\to G$ is the identity (columns indexed by $G$), so $\mathcal A_{\eta^{-1}(g+\eta(j))}$ reads $\mathcal A_{g+j}$. The equality is an equality of sets in every layer.
-- source:
--   Igarashi, Meunier, Envy-Free Division of Multi-Layered Cakes, arXiv:2106.02262v4, p. 7, Lemma 2

import Mathlib
import Definitions.Def_MultiLayerCake_LongKnives_Model

namespace MultiLayerCake.LongKnives

/-- Lemma 2, p. 7: the encoding is equivariant, `A_j(x) = A_{g+j}(g · x)` for every point `x` of
`‖Δ_{2q−1,q}‖`, every column/bundle `j ∈ G` and every `g ∈ G` (columns indexed by `G`, `η = id`). -/
theorem lemma_2 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {m : ℕ}
    (𝔓 : Procedure G) (h : Fin m → G) (hh : Function.Injective h) :
    ∀ x ∈ chessboard G, ∀ g j : G, encode 𝔓 h x j = encode 𝔓 h (actCB g x) (g + j) := by sorry

end MultiLayerCake.LongKnives
