-- Prove2me | Theorems.Thm_Menger27_Graphs_grad_eq_consists
-- name    : Menger27.Graphs.grad_eq_consists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:14:06.798505+00:00
-- url     : https://prove2.me/theorems/61b12aab-387f-4575-a3ae-75b4d0b933da
-- title:
--   p. 101, proof of Satz δ — an n-point connected graph with exactly n edges consists of n disjoint P–Q paths
-- statement:
--   Let $G$ be a finite simple graph on $V$, let $P, Q \subseteq V$ be disjoint, and let $n \ge 0$. Suppose $G$ is $n$-point connected between $P$ and $Q$ and has exactly $n$ edges. Then $G$ consists of $n$ pairwise disjoint paths between $P$ and $Q$: there are paths $W_1, \dots, W_n$ of $G$, each from a vertex of $P$ to a vertex of $Q$, with pairwise disjoint vertex sets, such that every edge of $G$ lies on one of them:
--   $$E(G) = E(W_1) \cup \dots \cup E(W_n) .$$
--
--   Menger writes: "und dass jeder zwischen P und Q n-punktig zusammenhängende Raum vom Grad n aus n paarweise fremden Bögen zwischen P und Q besteht". Together with the bound $|E(G)| \ge n$ this settles the base case of the induction on the degree.
--
--   **Formalization Note.** "Besteht aus" (consists of) is rendered as: the edges of $G$ are exactly covered by the $n$ paths. Vertices of $V$ on no edge are not points of Menger's space $K$, which is a union of arcs, so they are not required to lie on a path. The degree is the number of edges, as in the previous milestone.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 101, proof of Satz δ

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation

namespace Menger27.Graphs

theorem grad_eq_consists {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hG : NPointConnected G P Q n) (hgrad : G.edgeFinset.card = n) :
    ∃ (a b : Fin n → V) (w : ∀ i, G.Walk (a i) (b i)),
      (∀ i, a i ∈ P ∧ b i ∈ Q ∧ (w i).IsPath) ∧
      (∀ i j, i ≠ j → List.Disjoint (w i).support (w j).support) ∧
      ∀ e ∈ G.edgeSet, ∃ i, e ∈ (w i).edges := by sorry

end Menger27.Graphs
