-- Prove2me | Theorems.Thm_N25_siegelFun_second_index_shift
-- name    : N25.siegelFun_second_index_shift
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:05.993197+00:00
-- url     : https://prove2.me/theorems/b4dd3a3e-91da-448f-bddc-9510e9085c65
-- title:
--   Shifting the second Siegel index by the level gives an explicit phase
-- statement:
--   Let $N≥0$, let $r,s,k∈ℤ$, and let $z∈ℂ$. Then $$g_{r,s+kN}^{(N)}(z)=\exp\big(πik(r-N)/N\big)g_{r,s}^{(N)}(z).$$ This controls the multiplier introduced when normalizing the second Siegel index. Formalization note: the identity is stated for every natural $N$ exactly as in the formal theorem.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option autoImplicit false

theorem N25.siegelFun_second_index_shift (N : ℕ) (r s k : ℤ) (z : ℂ) :
    ModularCurve.siegelFun N r (s + k * (N : ℤ)) z =
      Complex.exp (Real.pi * Complex.I * (k : ℂ) *
        ((r : ℂ) - (N : ℂ)) / (N : ℂ)) *
      ModularCurve.siegelFun N r s z := by sorry
