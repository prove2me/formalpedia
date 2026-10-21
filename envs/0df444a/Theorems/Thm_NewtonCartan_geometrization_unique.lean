-- Prove2me | Theorems.Thm_NewtonCartan_geometrization_unique
-- name    : NewtonCartan.geometrization_unique
-- status  : Open
-- author  : @Ethan
-- created : 2026-10-21T05:37:45.028423+00:00
-- url     : https://prove2.me/theorems/9d3dd696-13b0-4864-80ca-7521fe6638b7
-- title:
--   Prop. 2.1 (G2): uniqueness of Trautman geometrization
-- statement:
--   Let $(\mathbb R^4,t_a,h^{ab},\nabla)$ be a flat classical spacetime with smooth potential $\varphi$ (an object of NG), and write $\tilde\nabla=(\nabla,-t_bt_c\nabla^a\varphi)$ for its Trautman geometrization. Then $\tilde\nabla$ is the unique torsion-free derivative operator on $\mathbb R^4$ whose unit timelike geodesics are exactly the curves satisfying Newton's law $\xi^n\nabla_n\xi^a=-\nabla^a\varphi$.
-- source:
--   J. O. Weatherall, arXiv:1411.5757, Prop. 2.1 uniqueness clause (p. 4); D. B. Malament, Topics in the Foundations of GR and Newtonian Gravitation Theory (2012), Prop. 4.2.1 (G2)

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- Uniqueness clause of Prop. 2.1 / Malament 4.2.1 (G2): `geomΓ` is the unique derivative
operator whose unit timelike geodesics are exactly the Newtonian trajectories of `(Γ, φ)`. -/
theorem geometrization_unique (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ) :
    ∀ Γ' : Conn, IsDerivOp Γ' → SameTrajectories Γ φ Γ' → Γ' = geomΓ Γ φ := by sorry

end NewtonCartan
