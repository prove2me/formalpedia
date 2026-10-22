-- Prove2me | Theorems.Thm_NewtonCartan_recovery
-- name    : NewtonCartan.recovery
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-20T23:17:08.034587+00:00
-- url     : https://prove2.me/theorems/8ef97a8c-b1be-4ae1-ab99-4bc693f332ab
-- title:
--   Prop. 2.2: Trautman recovery
-- statement:
--   Spacetime is $\mathbb R^4$ in a global chart (index 0 = time) with $t_a=dx^0$, $h^{ab}=\mathrm{diag}(0,1,1,1)$; a derivative operator is a smooth symmetric Christoffel field $\Gamma^a{}_{bc}$; curvature in Malament's convention $\xi^bR^a{}_{bcd}=-2\nabla_{[c}\nabla_{d]}\xi^a$, $R_{bc}=R^n{}_{bcn}$; $\tilde\Gamma=\Gamma+t_bt_c\nabla^a\varphi$ is the geometrization; timelike curves have unit tangent $t_a\xi^a=1$. If $\tilde\nabla$ is a classical spacetime satisfying (1)-(3) for some smooth $\rho$, there are a smooth $\varphi$ and a flat compatible $\nabla$ such that the timelike geodesics of $\tilde\nabla$ are exactly the curves with $\xi^n\nabla_n\xi^a=-\nabla^a\varphi$, and $\nabla^a\nabla_a\varphi=4\pi\rho$.
-- source:
--   J. O. Weatherall, Are Newtonian Gravitation and Geometrized Newtonian Gravitation Theoretically Equivalent?, Erkenntnis 81 (2016) 1073-1091, https://arxiv.org/abs/1411.5757, Prop. 2.2 (pp. 4-5); D. B. Malament, Topics in the Foundations of General Relativity and Newtonian Gravitation Theory (2012), Ch. 4, Prop. 4.2.5

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- **Prop. 2.2 (Trautman).** Let `(ℝ⁴, t_a, h^{ab}, ∇̃)` be a classical spacetime satisfying
conditions (1)–(3) of Prop. 2.1 for some smooth `ρ`. Then there are a smooth `φ` and a flat derivative
operator `∇` such that `(ℝ⁴, t_a, h^{ab}, ∇)` is a classical spacetime, the timelike geodesics of `∇̃`
are exactly the curves with `ξ^n ∇_n ξ^a = -∇^a φ`, and `∇, φ` satisfy Poisson's equation. -/
theorem recovery (Γt : Conn) (ρ : E → ℝ) (hΓt : IsClassical Γt) (hρ : ContDiff ℝ ∞ ρ)
    (hcurv : CurvConds Γt ρ) :
    ∃ (Γ : Conn) (φ : E → ℝ), IsNG Γ φ ∧ SameTrajectories Γ φ Γt ∧ Poisson Γ φ ρ := by sorry

end NewtonCartan
