-- Prove2me | Theorems.Thm_N25_gamma_mem_M
-- name    : N25.gamma_mem_M
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:05.454878+00:00
-- url     : https://prove2.me/theorems/64f09775-cb2e-479a-a779-f51c8e6821f6
-- title:
--   The order-five diamond operator preserves rational fixed points
-- statement:
--   Let $J$ be the geometric Jacobian carrier for the level-$25$ modular curve, let $G_{ℚ}=Gal(ℚ̄/ℚ)$, let $M=J^{G_{ℚ}}$, and let $γ:J→J$ be the selected diamond operator. For every $x∈J$ fixed by $G_{ℚ}$, $$x∈M\quad⇒\quad γ(x)∈M.$$ This makes the diamond action available on the rational Mordell–Weil subgroup.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_N25_LocalKummerEquivariance

set_option autoImplicit false
open N25

theorem N25.gamma_mem_M {x : N25.J} (hx : x ∈ N25.M) : N25.gamma x ∈ N25.M := by sorry
