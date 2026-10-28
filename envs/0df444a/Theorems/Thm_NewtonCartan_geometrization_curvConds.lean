-- Prove2me | Theorems.Thm_NewtonCartan_geometrization_curvConds
-- name    : NewtonCartan.geometrization_curvConds
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:37:46.131734+00:00
-- url     : https://prove2.me/theorems/e010e8f6-a642-4be3-96ee-bb34aa5a426b
-- title:
--   Prop. 2.1 (G3): curvature conditions after Trautman geometrization
-- statement:
--   Let $(\mathbb R^4,t_a,h^{ab},\nabla)$ be a flat classical spacetime and let smooth $\varphi,\rho$ satisfy Poisson's equation $\nabla^a\nabla_a\varphi=4\pi\rho$. Write $\tilde\nabla=(\nabla,-t_bt_c\nabla^a\varphi)$ for the Trautman geometrization. Then the curvature of $\tilde\nabla$ satisfies (1) $R_{ab}=4\pi\rho t_a t_b$, (2) $R^a{}_b{}^c{}_d=R^c{}_d{}^a{}_b$, and (3) $R^{ab}{}_{cd}=0$.
-- source:
--   J. O. Weatherall, arXiv:1411.5757, Prop. 2.1 curvature conditions (1)–(3) (p. 4); D. B. Malament, Topics… (2012), Prop. 4.2.1 (G3), eqs. (4.2.4)–(4.2.6)

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- Curvature conditions of Prop. 2.1 / Malament 4.2.1 (G3): after Trautman geometrization,
`(1) R_{ab}=4πρ t_a t_b`, `(2) R^a{}_b{}^c{}_d=R^c{}_d{}^a{}_b`, `(3) R^{ab}{}_{cd}=0`. -/
theorem geometrization_curvConds (Γ : Conn) (φ ρ : E → ℝ) (hNG : IsNG Γ φ)
    (hρ : ContDiff ℝ ∞ ρ) (hP : Poisson Γ φ ρ) :
    CurvConds (geomΓ Γ φ) ρ := by sorry

end NewtonCartan
