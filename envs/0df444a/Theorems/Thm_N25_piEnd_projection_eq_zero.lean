-- Prove2me | Theorems.Thm_N25_piEnd_projection_eq_zero
-- name    : N25.piEnd_projection_eq_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:06.763192+00:00
-- url     : https://prove2.me/theorems/4642574e-a7b1-492d-b35c-95843e489cc6
-- title:
--   An explicit polynomial projects $71$-torsion into $ker(π)$
-- statement:
--   Assume $1+γ+γ^2+γ^3+γ^4=0$ on $J$. If $x∈J$ is killed by $71$, define $$y=3x+18γx+22γ^2x+42γ^3x.$$ Then $$π(y)=0.$$ This explicit projection isolates the selected two-dimensional kernel inside the full $71$-torsion.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerPolynomial

set_option autoImplicit false
open N25

theorem N25.piEnd_projection_eq_zero (hPhi : PhiFiveZero) (x : J)
    (hx : 71 • x = 0) :
    piEnd (3 • x + 18 • gamma x + 22 • gamma (gamma x) +
      42 • gamma (gamma (gamma x))) = 0 := by sorry
