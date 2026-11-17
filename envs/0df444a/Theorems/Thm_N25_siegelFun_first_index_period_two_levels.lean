-- Prove2me | Theorems.Thm_N25_siegelFun_first_index_period_two_levels
-- name    : N25.siegelFun_first_index_period_two_levels
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:28.240674+00:00
-- url     : https://prove2.me/theorems/67763b11-ac9e-480f-83a6-1ccfb9e321fc
-- title:
--   The first Siegel index has period $2N$ when the second index is zero
-- statement:
--   Let $N≥0$ be an integer level, let $r,k∈ℤ$, and let $τ$ lie in the upper half-plane. Then the Siegel function satisfies $$g_{r+2kN,0}^{(N)}(τ)=g_{r,0}^{(N)}(τ).$$ This periodicity reduces first indices to a finite set of residues.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option autoImplicit false

theorem N25.siegelFun_first_index_period_two_levels
    (N : ℕ) (r k : ℤ) (τ : UpperHalfPlane) :
    ModularCurve.siegelFun N (r + 2*k*(N : ℤ)) 0 (τ : ℂ) =
      ModularCurve.siegelFun N r 0 (τ : ℂ) := by sorry
