-- Prove2me | Theorems.Thm_LPCommunity_LPFail_display_19
-- name    : LPCommunity.LPFail.display_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:05:11.902128+00:00
-- url     : https://prove2.me/theorems/d9fdb486-af07-422d-9c56-9d165fd953c7
-- title:
--   Display (19), p. 12 — the triangle sums of x̃ are at most (3/2)(ρ_max + c)/(ρ_avg + c(1 − 1/n))
-- statement:
--   Let $G=(V,E)$ be a connected graph on $n\ge 5$ nodes, with diameter $\rho_{\max}(G)$, average distance $\rho_{\mathrm{avg}}(G)$, constant $c(G)$ of (17), and let $\tilde x$ be the point of the proof of Theorem 5. Then for all $1\le i<j<k\le n$,
--   $$\tilde x_{ij}+\tilde x_{ik}+\tilde x_{jk}\le\frac32\cdot\frac{\rho_{\max}(G)+c(G)}{\rho_{\mathrm{avg}}(G)+c(G)(1-\frac1n)}.$$
--
--   This is the first step of checking that $\tilde x$ satisfies the constraints (2) of (LP-P); the choice of $c(G)$ then makes the right-hand side at most $2$.
--
--   **Formalization Note** The diameter enters through its real value, finite for a connected graph.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 12, §3.2, proof of Theorem 5, display (19)

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_LPFail_XTilde

open Finset
open scoped Classical ENNReal

namespace LPCommunity.LPFail
theorem display_19 {n : ℕ} (G : SimpleGraph (Fin n)) (hconn : G.Connected) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    xTilde G i j + xTilde G i k + xTilde G j k ≤
      3 / 2 * ((((rhoMax G : ℕ∞) : ℝ≥0∞).toReal + cG G) /
        ((rhoAvg G).toReal + cG G * (1 - 1 / (n : ℝ)))) := by sorry
end LPCommunity.LPFail
