-- Prove2me | Theorems.Thm_NicerEars_TwoEC_tcut_two_packing
-- name    : NicerEars.TwoEC.tcut_two_packing
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T11:18:20.446312+00:00
-- url     : https://prove2.me/theorems/fbfeda1b-ae5e-4d84-a422-bd4b3080ed16
-- title:
--   Edmonds–Johnson / Lovász — 2τ(G,T) T-cuts covering every edge at most twice
-- statement:
--   This is the 2-packing theorem for $T$-cuts of Edmonds–Johnson and Lovász, as used in the proof of Theorem 19 of Sebő–Vygen.
--
--   Let $G$ be a finite connected graph, possibly with parallel edges but without loops, and let $T\subseteq V(G)$ with $|T|$ even. A *$T$-cut* is a cut $\delta(W)$ with $|W\cap T|$ odd. Write $\tau(G,T)$ for the minimum cardinality of a $T$-join in $G$, i.e. of an edge set $J\subseteq E(G)$ whose set of odd-degree vertices is exactly $T$. Then there is a multiset $\mathcal W$ of vertex sets $W$ such that:
--
--   1. $|\mathcal W| = 2\,\tau(G,T)$;
--   2. every $W\in\mathcal W$ satisfies $|W\cap T|$ odd, so $\delta(W)$ is a $T$-cut;
--   3. every edge $e\in E(G)$ lies in $\delta(W)$ for at most two members $W$ of $\mathcal W$, counted with multiplicity.
--
--   Equivalently, the maximum size of a family of $T$-cuts covering each edge at most twice equals $2\tau(G,T)$; the inequality "$\le$" is the easy direction. In the proof of Theorem 19, summing the cut constraints $x(\delta(W))\ge2$ over such a family gives $\mathrm{LP}(G)\ge 2\tau(G,T)$.
--
--   **Formalization Note** The multiset is a `Multiset (Finset V)` of shores $W$; a cut $\delta(W)$ is the platform's `Graph.cut W` (edges with exactly one end in $W$), and $\tau(G,T)$ is `Graph.tau G T`.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 16, proof of Theorem 19 ('By a well-known result due to Edmonds and Johnson [1973] and Lovász [1975], this implies that there exists a multiset of L_phi(G) T-cuts containing every edge at most twice'); L. Lovász, 2-matchings and 2-covers of hypergraphs, Acta Math. Acad. Sci. Hungar. 26 (1975) 433-444

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Setting

namespace NicerEars.TwoEC

open Finset

theorem tcut_two_packing {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : G.IsConnected) (T : Finset V) (hT : Even #T) :
    ∃ L : Multiset (Finset V), Multiset.card L = 2 * G.tau T ∧ (∀ W ∈ L, Odd #(W ∩ T)) ∧
      ∀ e : E, Multiset.card (L.filter (fun W => e ∈ G.cut W)) ≤ 2 := by sorry

end NicerEars.TwoEC
