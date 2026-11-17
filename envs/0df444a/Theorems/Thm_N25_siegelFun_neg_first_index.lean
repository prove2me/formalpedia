-- Prove2me | Theorems.Thm_N25_siegelFun_neg_first_index
-- name    : N25.siegelFun_neg_first_index
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:30.797511+00:00
-- url     : https://prove2.me/theorems/9a63c824-232f-4191-97a9-be65d0daedb5
-- title:
--   Negating the first Siegel index changes the sign
-- statement:
--   For every natural level $N$, integer $r$, and complex number $z$, $$g_{-r,0}^{(N)}(z)=-g_{r,0}^{(N)}(z).$$ This sign rule is used together with periodicity to reflect indices into a preferred range.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option autoImplicit false

theorem N25.siegelFun_neg_first_index (N : ℕ) (r : ℤ) (z : ℂ) :
    ModularCurve.siegelFun N (-r) 0 z = -ModularCurve.siegelFun N r 0 z := by sorry
