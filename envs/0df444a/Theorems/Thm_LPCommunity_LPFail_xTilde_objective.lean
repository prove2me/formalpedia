-- Prove2me | Theorems.Thm_LPCommunity_LPFail_xTilde_objective
-- name    : LPCommunity.LPFail.xTilde_objective
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:05:11.195097+00:00
-- url     : https://prove2.me/theorems/415d982d-eab4-48fc-8664-07b941553ffe
-- title:
--   Proof of Theorem 5, p. 13 — the objective of (LP-P) at x̃ equals (1 + c(G))/(ρ_avg + c(1 − 1/n)) · |E|/2
-- statement:
--   Let $G=(V,E)$ be a connected graph on $n\ge 5$ nodes and $\tilde x$ the point of the proof of Theorem 5. The objective value of (LP-P) at $\tilde x$ is
--   $$\sum_{(i,j)\in E}\tilde x_{ij}=\frac{1+c(G)}{\rho_{\mathrm{avg}}(G)+c(G)(1-\frac1n)}\cdot\frac{|E|}{2}.$$
--
--   Together with the feasibility of $\tilde x$, this value is an upper bound on the optimal value of (LP-P), which is what Theorem 5 compares with the cost $|E_0|$ of the planted bisection.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 13, §3.2, proof of Theorem 5 (objective value of (LP-P) at x̃)

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_LPFail_XTilde

open Finset
open scoped Classical ENNReal

namespace LPCommunity.LPFail
theorem xTilde_objective {n : ℕ} (G : SimpleGraph (Fin n)) (hconn : G.Connected) (hn : 5 ≤ n) :
    LPCommunity.LPRecovery.lpObj G (xTilde G) =
      (1 + cG G) / ((rhoAvg G).toReal + cG G * (1 - 1 / (n : ℝ))) * (G.edgeFinset.card : ℝ) / 2 := by sorry
end LPCommunity.LPFail
