-- Prove2me | Theorems.Thm_N25_siegelFun_first_index_shift
-- name    : N25.siegelFun_first_index_shift
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:29.278523+00:00
-- url     : https://prove2.me/theorems/61c508be-94cb-4661-a09e-5f4ffa4f36ab
-- title:
--   Shifting the first Siegel index by the level gives an explicit phase
-- statement:
--   Let $N≥0$, let $r,s,k∈ℤ$, and let $τ$ lie in the upper half-plane. Then $$g_{r+kN,s}^{(N)}(τ)=\big(-\exp(-πis/N)\big)^k g_{r,s}^{(N)}(τ).$$ This controls the multiplier introduced when normalizing the first Siegel index. Formalization note: the identity is stated for every natural $N$ exactly as in the formal theorem.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option autoImplicit false

theorem N25.siegelFun_first_index_shift (N : ℕ) (r s k : ℤ) (τ : UpperHalfPlane) :
    ModularCurve.siegelFun N (r + k * (N : ℤ)) s (τ : ℂ) =
      (-Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ)))) ^ k *
        ModularCurve.siegelFun N r s (τ : ℂ) := by sorry
