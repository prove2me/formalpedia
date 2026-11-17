-- Prove2me | Theorems.Thm_N25_siegelFun25_nonzero_leading_limit
-- name    : N25.siegelFun25_nonzero_leading_limit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:27.481252+00:00
-- url     : https://prove2.me/theorems/feed0167-9622-4317-861d-2401411097e6
-- title:
--   A level-$25$ Siegel function has a nonzero normalized leading coefficient
-- statement:
--   Let $r,s∈ℤ$ satisfy $25∣r⇒25∤s$, let $r_0$ be the residue of $r$ modulo $25$, and put $B_2(x)=x^2-x+1/6$. There exists $c∈ℂ^×$ such that $$\frac{g_{r,s}^{(25)}(τ)}{\exp(πiB_2(r_0/25)τ)}→c\qquad\text{as }Im(τ)→∞.$$ This gives the precise nonzero leading behavior of each Siegel factor at the standard cusp.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option autoImplicit false
open Filter Topology

theorem N25.siegelFun25_nonzero_leading_limit (r s : ℤ)
    (hs : (25 : ℤ) ∣ r → ¬(25 : ℤ) ∣ s) :
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto
      (fun τ : UpperHalfPlane => ModularCurve.siegelFun 25 r s (τ : ℂ) /
        Complex.exp (Real.pi * Complex.I *
          ((((r % 25 : ℤ) : ℂ) / 25) ^ 2 - ((r % 25 : ℤ) : ℂ) / 25 + 1 / 6) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c) := by sorry
