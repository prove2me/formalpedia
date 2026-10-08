-- Prove2me | Theorems.Thm_FriezeKannan_PseudoReg_eq_47
-- name    : FriezeKannan.PseudoReg.eq_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:49.136327+00:00
-- url     : https://prove2.me/theorems/01120ab7-2ea1-4f52-af1b-d03dc08df1e6
-- title:
--   (47), p. 203 — A(S,T) = e(S,T), A_Q(S,T) = Σ d_{i,j}|S_i||T_j|, and A(S,T) − A_Q(S,T) = Δ_Q(S,T)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with adjacency matrix $\mathbf A$, let $\mathcal Q=W_1,\dots,W_q$ be a partition of $V$ with index set $K$, and let $d_{i,j}$ be the density between $W_i$ and $W_j$. For disjoint $S,T\subseteq V$, with $S_i=S\cap W_i$ and $T_j=T\cap W_j$,
--   $$\mathbf A(S,T)=e(S,T),\qquad \mathbf A_{\mathcal Q}(S,T)=\sum_{i\in K}\sum_{j\in K}d_{i,j}|S_i||T_j|,$$
--   and consequently
--   $$\mathbf A(S,T)-\mathbf A_{\mathcal Q}(S,T)=\Delta_{\mathcal Q}(S,T).$$
--
--   The identity rewrites the deviation from regularity $\Delta_{\mathcal Q}$ as a block sum of the matrix $\mathbf A-\mathbf A_{\mathcal Q}$, which turns pseudo-regularity into a statement about the cut norm of $\mathbf A-\mathbf A_{\mathcal Q}$.
--
--   **Formalization Note.** $e(S,T)$ is the number of ordered adjacent pairs in $S\times T$ (Mathlib's `interedges`), which for disjoint $S,T$ is the number of edges between them. The diagonal densities $d_{i,i}$ are block averages $\mathbf A(W_i,W_i)/|W_i|^2$, as explained in the definitions item; with the paper's printed $d(A,A)=e(A,A)/\binom{|A|}{2}$ the identity fails. The disjointness hypothesis is kept as on the page.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 203, §5.1, display (47) and the two equalities before it

import Mathlib
import Definitions.Def_FriezeKannan_PseudoReg_Setting

namespace FriezeKannan.PseudoReg

theorem eq_47 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : Finpartition (Finset.univ : Finset V)) (S T : Finset V) (hST : Disjoint S T) :
    blockSum (G.adjMatrix ℝ) S T = ((G.interedges S T).card : ℝ) ∧
    blockSum (blockAvg Q (G.adjMatrix ℝ)) S T =
      ∑ Vi ∈ Q.parts, ∑ Vj ∈ Q.parts,
        (G.edgeDensity Vi Vj : ℝ) * ((S ∩ Vi).card : ℝ) * ((T ∩ Vj).card : ℝ) ∧
    blockSum (G.adjMatrix ℝ) S T - blockSum (blockAvg Q (G.adjMatrix ℝ)) S T =
      delta G Q S T := by sorry

end FriezeKannan.PseudoReg
