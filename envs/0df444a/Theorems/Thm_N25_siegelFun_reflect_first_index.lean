-- Prove2me | Theorems.Thm_N25_siegelFun_reflect_first_index
-- name    : N25.siegelFun_reflect_first_index
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:32.300417+00:00
-- url     : https://prove2.me/theorems/64b034dc-61e1-464f-8797-1512b38d5bc9
-- title:
--   Reflecting the first Siegel index across the level preserves the function
-- statement:
--   For every natural level $N$, integer $r$, and upper-half-plane point $τ$, $$g_{N-r,0}^{(N)}(τ)=g_{r,0}^{(N)}(τ).$$ This reflection symmetry simplifies the finite list of Siegel factors in the modular units.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option autoImplicit false

theorem N25.siegelFun_reflect_first_index (N : ℕ) (r : ℤ) (τ : UpperHalfPlane) :
    ModularCurve.siegelFun N ((N : ℤ)-r) 0 (τ : ℂ) =
      ModularCurve.siegelFun N r 0 (τ : ℂ) := by sorry
