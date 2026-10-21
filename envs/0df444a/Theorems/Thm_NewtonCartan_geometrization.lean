-- Prove2me | Theorems.Thm_NewtonCartan_geometrization
-- name    : NewtonCartan.geometrization
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-20T23:16:52.451723+00:00
-- url     : https://prove2.me/theorems/8dbeff9c-40dd-49ea-89cf-5e7c63297750
-- title:
--   Prop. 2.1: Trautman geometrization
-- statement:
--   Spacetime is $\mathbb R^4$ in a global chart (index 0 = time) with $t_a=dx^0$, $h^{ab}=\mathrm{diag}(0,1,1,1)$; a derivative operator is a smooth symmetric Christoffel field $\Gamma^a{}_{bc}$; curvature in Malament's convention $\xi^bR^a{}_{bcd}=-2\nabla_{[c}\nabla_{d]}\xi^a$, $R_{bc}=R^n{}_{bcn}$; $\tilde\Gamma=\Gamma+t_bt_c\nabla^a\varphi$ is the geometrization; timelike curves have unit tangent $t_a\xi^a=1$. If $\nabla$ is flat and compatible with $t_a,h^{ab}$, and smooth $\varphi,\rho$ satisfy $\nabla^a\nabla_a\varphi=4\pi\rho$, then $\tilde\nabla=(\nabla,-t_bt_c\nabla^a\varphi)$ is a classical spacetime; its timelike geodesics are exactly the curves with $\xi^n\nabla_n\xi^a=-\nabla^a\varphi$; it is the unique derivative operator with this property; and it satisfies (1) $R_{ab}=4\pi\rho t_at_b$, (2) $R^a{}_b{}^c{}_d=R^c{}_d{}^a{}_b$, (3) $R^{ab}{}_{cd}=0$.
-- source:
--   J. O. Weatherall, Are Newtonian Gravitation and Geometrized Newtonian Gravitation Theoretically Equivalent?, Erkenntnis 81 (2016) 1073-1091, https://arxiv.org/abs/1411.5757, Prop. 2.1 (p. 4); D. B. Malament, Topics in the Foundations of General Relativity and Newtonian Gravitation Theory (2012), Ch. 4, Prop. 4.2.1

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- **Prop. 2.1 (Trautman).** Let `(ℝ⁴, t_a, h^{ab}, ∇)` be a flat classical spacetime and let
`ρ, φ` be smooth scalar fields satisfying Poisson's equation. Then `∇̃ = (∇, -t_b t_c ∇^a φ)` is a
classical spacetime; `∇̃` is the unique derivative operator whose (unit) timelike geodesics are
exactly the curves with `ξ^n ∇_n ξ^a = -∇^a φ`; and `∇̃` satisfies (1)–(3). -/
theorem geometrization (Γ : Conn) (φ ρ : E → ℝ) (hNG : IsNG Γ φ) (hρ : ContDiff ℝ ∞ ρ)
    (hP : Poisson Γ φ ρ) :
    IsClassical (geomΓ Γ φ) ∧ SameTrajectories Γ φ (geomΓ Γ φ) ∧
    (∀ Γ' : Conn, IsDerivOp Γ' → SameTrajectories Γ φ Γ' → Γ' = geomΓ Γ φ) ∧
    CurvConds (geomΓ Γ φ) ρ := by sorry

end NewtonCartan
