-- Prove2me | Theorems.Thm_NicerEars_TwoEC_theorem_20
-- name    : NicerEars.TwoEC.theorem_20
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T11:22:47.36435+00:00
-- url     : https://prove2.me/theorems/dba5b31c-ac5f-40d2-80a7-27eba2e2cd5d
-- title:
--   Theorem 20, p. 16 — L_µ(G,M) ≤ LP(G,T)
-- statement:
--   Theorem 20 of Sebő–Vygen (the earmuff lower bound).
--
--   Let $G$ be a finite connected graph, possibly with parallel edges but without loops. Let $T\subseteq V(G)$ with $|T|$ even, and let $M$ be an eardrum in $G$ with $V_M\cap T=\emptyset$, where $V_M=\bigcup M$, and with $\mathcal P_f\neq\emptyset$ for all $f\in M$. Here $\mathcal P_f$ is the set of paths $P$ in $G$ with $\mathrm{in}(P)=f$. Then
--
--   $$L_\mu(G,M):=|V(G)|-1+|M|-\mu(G,M)\ \le\ \mathrm{LP}(G,T),$$
--
--   where $\mu(G,M)$ is the maximum size of an earmuff for $M$. Here $\mathrm{LP}(G,T)$ is the minimum of $x(E(G))$ over $x\ge0$ such that:
--
--   1. $x(\delta(W))\ge2$ for every $\emptyset\ne W\subsetneq V(G)$ with $|W\cap T|$ even;
--   2. $x(\delta(\mathcal W))\ge|\mathcal W|-1$ for every partition $\mathcal W$ of $V(G)$.
--
--   In particular, every connected-$T$-join of $G$ has at least $L_\mu(G,M)$ edges.
--
--   This lower bound is used, with $T=\emptyset$, to bound the size of the tour constructed in Theorem 24. Corollary 21 is the case $T=\emptyset$.
--
--   **Formalization Note** "$L_\mu\le\mathrm{LP}(G,T)$" is stated as $L_\mu(G,M)\le x(E(G))$ for every feasible point $x$ of $\mathrm{LP}(G,T)$ (platform predicate `Graph.LPTFeasible`). $V_M\cap T=\emptyset$ is stated as $f\cap T=\emptyset$ for each $f\in M$. A connected-$T$-join is a multiset of edges of $G$ with multiplicities at most $2$, i.e. a subset of $E(2G)$.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 16, Theorem 20

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Earmuff

namespace NicerEars.TwoEC

open Finset

theorem theorem_20 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : G.IsConnected) (T : Finset V) (hT : Even #T)
    (M : Finset (Finset V)) (hM : IsEardrum G M) (hMT : ∀ f ∈ M, Disjoint f T)
    (hP : ∀ f ∈ M, (PathsThrough G f).Nonempty) :
    (∀ x : E → ℝ, G.LPTFeasible T x → (Lmu G M : ℝ) ≤ ∑ e, x e) ∧
      ∀ F : Finset (E × Fin 2), G.IsConnectedTJoin T F → Lmu G M ≤ #F := by sorry

end NicerEars.TwoEC
