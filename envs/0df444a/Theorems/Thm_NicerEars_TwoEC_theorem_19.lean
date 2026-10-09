-- Prove2me | Theorems.Thm_NicerEars_TwoEC_theorem_19
-- name    : NicerEars.TwoEC.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:06.051516+00:00
-- url     : https://prove2.me/theorems/162f9873-a1a0-4dcd-b855-3f6aa1b410a3
-- title:
--   Theorem 19 (Cheriyan, Sebő and Szigeti 2001) — L_ϕ(G) = |V(G)| + ϕ(G) − 1 ≤ LP(G)
-- statement:
--   Let $G$ be a 2-edge-connected graph and $L_\varphi(G):=|V(G)|+\varphi(G)-1$, where $\varphi(G)$ is the minimum number of even ears in an ear-decomposition of $G$. Then
--
--   $$L_\varphi(G)\le\mathrm{LP}(G).$$
--
--   In particular, every 2-edge-connected spanning subgraph of $G$ has at least $L_\varphi(G)$ edges.
--
--   This is one of the two lower bounds against which the 4/3-approximation for 2ECSS is measured.
--
--   **Formalization Note** "$L_\varphi(G)\le\mathrm{LP}(G)$" is stated as $L_\varphi(G)\le x(E(G))$ for every feasible point $x$ of $\mathrm{LP}(G)$, which is equivalent because $\mathrm{LP}(G)$ is the minimum of $x(E(G))$ over the feasible points. The second part is stated for every edge set $F\subseteq E(G)$ spanning a 2-edge-connected subgraph.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 16, Theorem 19 (Cheriyan, Sebő and Szigeti [2001])

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Earmuff

namespace NicerEars.TwoEC

open Finset

theorem theorem_19 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : G.IsTwoEdgeConnected) :
    (∀ x : E → ℝ, G.LPFeasible x → (Lphi G : ℝ) ≤ ∑ e, x e) ∧
      ∀ F : Finset E, G.IsTwoECSpanning F → Lphi G ≤ #F := by sorry

end NicerEars.TwoEC
