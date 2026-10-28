-- Prove2me | Theorems.Thm_NCPSeqOpt_AugLag_nonexpansive_proj
-- name    : NCPSeqOpt.AugLag.nonexpansive_proj
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:10.884601+00:00
-- url     : https://prove2.me/theorems/bbe7bf22-7c77-4ad6-8e13-29eec8a73bf2
-- title:
--   §2.1, p. 3 — the projection onto a closed convex cone is nonexpansive
-- statement:
--   Let $\mathbb E$ be a finite-dimensional real inner product space and $\mathcal K\subseteq\mathbb E$ a nonempty closed convex cone, with orthogonal projection $\Pi_{\mathcal K}$. Then
--   $$\|\Pi_{\mathcal K}(w)-\Pi_{\mathcal K}(v)\|\le\|w-v\|\qquad\text{for all }v,w\in\mathbb E.$$
--
--   In particular $\Pi_{\mathcal K}$ is Lipschitz continuous. Both convergence proofs of the augmented Lagrangian method use this estimate, for $\mathcal K$ and for $\mathcal K^\circ$.
--
--   **Formalization Note** $\Pi_{\mathcal K}$ is `proj K`, a nearest point chosen by choice; for a nonempty closed convex set the nearest point exists and is unique.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), §2.1, p. 3 (display before (1))

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting

namespace NCPSeqOpt.AugLag

open MoreauProx.Decomposition
open scoped InnerProductSpace
open Filter Topology

theorem nonexpansive_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hK : IsClosedConvexCone K) (v w : E) :
    ‖proj K w - proj K v‖ ≤ ‖w - v‖ := by sorry

end NCPSeqOpt.AugLag
