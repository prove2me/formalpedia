-- Prove2me | Theorems.Thm_NicerEars_TSP_corollary_21
-- name    : NicerEars.TSP.corollary_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:29.348251+00:00
-- url     : https://prove2.me/theorems/2aeae719-a54d-43d4-808d-8ca9c5b1b96f
-- title:
--   Corollary 21 — L_µ(G, M) ≤ LP(G) for an eardrum M with all 𝒫_f ≠ ∅
-- statement:
--   **Corollary 21.** Let $G$ be a 2-edge-connected graph and $M$ an eardrum in $G$ with $\mathcal P_f\ne\emptyset$ for all $f\in M$. Then
--
--   $$L_\mu(G,M):=|V(G)|-1+|M|-\mu(G,M)\ \le\ \mathrm{LP}(G).$$
--
--   In particular, every 2-edge-connected spanning subgraph of $G$ has at least $L_\mu(G,M)$ edges.
--
--   Here $\mathcal P_f$ is the set of paths with internal vertex set $f$ and $\mu(G,M)$ is the maximum size of an earmuff for $M$. This is the second lower bound of the 7/5 analysis; it is the case $T=\emptyset$ of Theorem 20.
--
--   **Formalization Note.** "$\le\mathrm{LP}(G)$" is stated as $L_\mu(G,M)\le x(E(G))$ for every LP-feasible $x$. A 2-edge-connected spanning subgraph of $G$ is an edge set $F\subseteq E(G)$.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 17, Corollary 21

import Mathlib
import Definitions.Def_NicerEars_TSP_Earmuff

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Corollary 21, p. 17: for a 2-edge-connected graph G and an eardrum M in G with 𝒫_f ≠ ∅ for
all f ∈ M, L_µ(G, M) ≤ LP(G); in particular every 2-edge-connected spanning subgraph of G has at
least L_µ(G, M) edges. -/
theorem corollary_21 (G : Graph V E) (hG : G.IsTwoEdgeConnected) (M : Finset (Finset V))
    (hM : G.IsEardrum M) (hP : ∀ f ∈ M, (G.PathsThrough f).Nonempty) :
    (∀ x : E → ℝ, G.LPFeasible x → (G.Lmu M : ℝ) ≤ ∑ e, x e) ∧
    ∀ F : Finset E, G.IsTwoECSpanning F → G.Lmu M ≤ #F := by sorry

end NicerEars.TSP
