-- Prove2me | Theorems.Thm_HararySachs_Hyper_lemma_13
-- name    : HararySachs.Hyper.lemma_13
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T03:12:42.029411+00:00
-- url     : https://prove2.me/theorems/0478734d-a08b-4269-8673-21f37b38b313
-- title:
--   Lemma 13, labeled form — $\operatorname{Tr}_d(\mathcal H)=d(k-1)^n\sum_S C_S$ over connected Veblen infragraphs
-- statement:
--   This is the labeled form of Lemma 13 of Clark and Cooper. It expresses the $d$-th differential trace of a hypergraph as a weighted count of connected Veblen infragraphs.
--
--   Let $k\ge 2$, $n\ge 1$ and $d\ge 1$, and let $\mathcal H=([n],E)$ be a simple $k$-graph, i.e. every edge $e\in E$ is a $k$-element subset of $[n]$. Write $\operatorname{Tr}_d(\mathcal H)$ for the $d$-th trace of the normalized adjacency hypermatrix given by Equation (1) of the paper:
--
--   $$
--   \operatorname{Tr}_d(\mathcal H)=(k-1)^{n-1}\sum_{d_1+\cdots+d_n=d}\left(\prod_{i=1}^{n}\frac{\hat f_i^{\,d_i}}{(d_i(k-1))!}\right)\operatorname{tr}\bigl(A^{d(k-1)}\bigr).
--   $$
--
--   Here $A$ is an $n\times n$ matrix of independent variables, $\hat f_i$ is the $i$-th coordinate of $\mathcal A_{\mathcal H}x^{k-1}$ with $x_j$ replaced by $\partial/\partial A_{ij}$, and the operator is applied to $\operatorname{tr}(A^{d(k-1)})$, keeping the constant term.
--
--   A *labeled infragraph* of $\mathcal H$ with $d$ edges is a multiset $S$ of $d$ edges, each taken from $E$ and repetitions allowed. It is *Veblen* when every vertex degree is divisible by $k$, and *connected* when $S\neq\emptyset$ and any two covered vertices are joined by a chain of edges of $S$. Let $C_S$ be the associated coefficient of Definition 10, i.e. the sum of $\tau(D_R)/\prod_{v}\deg^-_{D_R}(v)$ over the Euler rootings $R$ of $S$. Then
--
--   $$
--   \operatorname{Tr}_d(\mathcal H)\;=\;d\,(k-1)^n\sum_{\substack{S\text{ labeled connected Veblen}\\ \text{infragraph of }\mathcal H,\ |S|=d}} C_S .
--   $$
--
--   This identity is the bridge between the algebraic trace in the resultant formula $\phi_d(\mathcal H)=P_d(-\operatorname{Tr}_1/1,\ldots,-\operatorname{Tr}_d/d)$ and the combinatorial Harary–Sachs expansion of Theorem 14. Inserting it into the Schur polynomial $P_d$ yields the labeled form of Theorem 14.
--
--   **Formalization Note** The paper states Lemma 13 as $d(k-1)^n\sum_{H\in\mathcal V_d(\mathcal H)}C_H\,(\#H\subseteq\mathcal H)$ over isomorphism classes. For a connected $H$, Definition 11 makes $(\#H\subseteq\mathcal H)$ the number of labeled copies of $H$ in $\mathcal H$, so the class-weighted sum equals the labeled sum used here. That labeled sum is the first display of the paper's proof, a sum over Euler rootings of all labeled connected Veblen infragraphs. Infragraphs are the elements of `allMultisets E d`, and $C_S$ is `assocCoeff S`, which equals `connectedCoeff S` for connected $S$. The trace is the mission definition `Tr`.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 11, Lemma 13 and the first display of its proof; Definitions 9-11, pp. 9-10; Equation (1), p. 4

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_Veblen

namespace HararySachs.Hyper
open Classical

theorem lemma_13 (n k d : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (hd : 1 ≤ d) :
    Tr (k := k) E d =
      (d : ℚ) * ((k : ℚ) - 1) ^ n *
        ∑ S ∈ (allMultisets E d).filter (fun S => IsVeblen S k ∧ IsConnected S),
          assocCoeff S := by sorry

end HararySachs.Hyper
