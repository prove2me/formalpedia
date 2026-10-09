-- Prove2me | Theorems.Thm_NicerEars_TwoEC_corollary_21
-- name    : NicerEars.TwoEC.corollary_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:23.569079+00:00
-- url     : https://prove2.me/theorems/d354d445-b51b-4a91-a6af-c1af07b839e0
-- title:
--   Corollary 21 — L_µ(G,M) ≤ LP(G) for an eardrum M with 𝒫_f ≠ ∅ for all f ∈ M
-- statement:
--   Let $G$ be a 2-edge-connected graph and $M$ an eardrum in $G$ such that for every $f\in M$ there is a path $P$ in $G$ with $\mathrm{in}(P)=f$. Let $\mu(G,M)$ be the maximum size of an earmuff for $M$ and $L_\mu(G,M):=|V(G)|-1+|M|-\mu(G,M)$. Then
--
--   $$L_\mu(G,M)\le\mathrm{LP}(G).$$
--
--   In particular, every 2-edge-connected spanning subgraph of $G$ has at least $L_\mu(G,M)$ edges.
--
--   This is the second lower bound used for 2ECSS; it accounts for the short ears that cannot all be made part of a forest.
--
--   **Formalization Note** "$\le\mathrm{LP}(G)$" is stated against every feasible point $x$ of $\mathrm{LP}(G)$. The paper derives the corollary from Theorem 20 with $T=\emptyset$; Theorem 20 itself is not part of this mission.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 17, Corollary 21 (L_µ defined in Theorem 20, p. 16)

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Earmuff

namespace NicerEars.TwoEC

open Finset

theorem corollary_21 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : G.IsTwoEdgeConnected) (M : Finset (Finset V)) (hM : IsEardrum G M)
    (hP : ∀ f ∈ M, (PathsThrough G f).Nonempty) :
    (∀ x : E → ℝ, G.LPFeasible x → (Lmu G M : ℝ) ≤ ∑ e, x e) ∧
      ∀ F : Finset E, G.IsTwoECSpanning F → Lmu G M ≤ #F := by sorry

end NicerEars.TwoEC
