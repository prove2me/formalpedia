-- Prove2me | Theorems.Thm_NicerEars_TSP_theorem_19
-- name    : NicerEars.TSP.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:53.627014+00:00
-- url     : https://prove2.me/theorems/61fd002f-ba83-4ca2-bc19-5a2f889122c6
-- title:
--   Theorem 19 (Cheriyan, Sebő, Szigeti) — L_ϕ(G) = |V(G)| + ϕ(G) − 1 ≤ LP(G)
-- statement:
--   **Theorem 19** (Cheriyan, Sebő and Szigeti [2001]). Let $G$ be a 2-edge-connected graph. Then
--
--   $$L_\varphi(G):=|V(G)|+\varphi(G)-1\ \le\ \mathrm{LP}(G).$$
--
--   In particular, every 2-edge-connected spanning subgraph of $G$ has at least $L_\varphi(G)$ edges.
--
--   This is one of the two lower bounds whose combination $\Lambda(G,M)=\frac23L_\mu(G,M)+\frac13L_\varphi(G)$ is compared with the tours constructed in the 7/5 analysis.
--
--   **Formalization Note.** "$\le\mathrm{LP}(G)$" is stated as $L_\varphi(G)\le x(E(G))$ for every LP-feasible $x$, which is equivalent since $\mathrm{LP}(G)$ is the minimum over feasible points. A 2-edge-connected spanning subgraph of $G$ is an edge set $F\subseteq E(G)$ (no doubling).
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 16, Theorem 19 (Cheriyan, Sebő and Szigeti [2001])

import Mathlib
import Definitions.Def_NicerEars_TSP_Earmuff

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 19 (Cheriyan, Sebő and Szigeti [2001]), p. 16: for a 2-edge-connected graph G,
L_ϕ(G) = |V(G)| + ϕ(G) − 1 ≤ LP(G); in particular every 2-edge-connected spanning subgraph of G has
at least L_ϕ(G) edges. -/
theorem theorem_19 (G : Graph V E) (hG : G.IsTwoEdgeConnected) :
    (∀ x : E → ℝ, G.LPFeasible x → (G.Lphi : ℝ) ≤ ∑ e, x e) ∧
    ∀ F : Finset E, G.IsTwoECSpanning F → G.Lphi ≤ #F := by sorry

end NicerEars.TSP
