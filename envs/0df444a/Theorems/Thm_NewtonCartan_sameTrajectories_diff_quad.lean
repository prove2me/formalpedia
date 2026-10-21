-- Prove2me | Theorems.Thm_NewtonCartan_sameTrajectories_diff_quad
-- name    : NewtonCartan.sameTrajectories_diff_quad
-- status  : Open
-- author  : @Ethan
-- created : 2026-10-21T05:58:00.79889+00:00
-- url     : https://prove2.me/theorems/a1ea4786-5f32-4e14-8b15-5947bf8bb45e
-- title:
--   SameTrajectories forces the spray of Γ' to match geomΓ on unit timelike vectors
-- statement:
--   Let $(\nabla,\varphi)$ be a flat classical spacetime with potential (an object of NG), and let $\nabla'$ be any torsion-free derivative operator whose unit-timelike geodesics are exactly the Newtonian trajectories of $(\nabla,\varphi)$. Writing $\widetilde{\nabla}$ for the Trautman geometrization of $(\nabla,\varphi)$, one has
--   $$
--   (\Gamma'^a{}_{bc}-\widetilde{\Gamma}^a{}_{bc})\,\xi^b\xi^c=0
--   $$
--   at every point, for every unit-timelike $\xi$ ($t_a\xi^a=1$).
--
--   The argument compares geodesic sprays: $\mathrm{SameTrajectories}$ identifies the unit-timelike geodesics of $\nabla'$ with those of $\widetilde{\nabla}$, and existence of a unit-timelike $\widetilde{\nabla}$-geodesic with arbitrary initial velocity forces the quadratic forms of the Christoffel symbols to agree on that cone.

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

theorem sameTrajectories_diff_quad (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (Γ' : Conn) (_hD : IsDerivOp Γ') (hS : SameTrajectories Γ φ Γ')
    (x : E) (a : Fin 4) (ξ : Fin 4 → ℝ) (hξ : ξ 0 = 1) :
    (∑ b : Fin 4, ∑ c : Fin 4,
        (Γ' x a b c - geomΓ Γ φ x a b c) * ξ b * ξ c) = 0 := by sorry

end NewtonCartan
