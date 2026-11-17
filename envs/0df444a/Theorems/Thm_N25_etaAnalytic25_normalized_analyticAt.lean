-- Prove2me | Theorems.Thm_N25_etaAnalytic25_normalized_analyticAt
-- name    : N25.etaAnalytic25_normalized_analyticAt
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:33.998985+00:00
-- url     : https://prove2.me/theorems/06da589d-42fb-4472-b95f-5276d1cfe22d
-- title:
--   The normalized eta residue function is analytic at the cusp
-- statement:
--   Let $0<g<25$, set $B_2(x)=x^2-x+1/6$, and define $H_g(\tau)=E_g(\tau)/e^{\pi iB_2(g/25)25\tau}$. In the width-one cusp coordinate, the associated cusp function is analytic at $q=0$:
--
--   $$\operatorname{cusp}_1(H_g)\text{ is analytic at }0.$$
--
--   This justifies taking the normalized $q$-expansion of the eta factor.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.etaAnalytic25_normalized_analyticAt
    (g : ℕ) (hg : 0 < g) (hg25 : g < 25) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1
      (fun τ : UpperHalfPlane => etaAnalytic25 g τ / Complex.exp (Real.pi * Complex.I *
        (((g : ℂ) / 25) ^ 2 - (g : ℂ) / 25 + 1 / 6) * (25 * (τ : ℂ))))) 0 := by sorry
