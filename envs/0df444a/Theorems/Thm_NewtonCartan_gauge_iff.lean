-- Prove2me | Theorems.Thm_NewtonCartan_gauge_iff
-- name    : NewtonCartan.gauge_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-20T23:17:22.161896+00:00
-- url     : https://prove2.me/theorems/e5dda248-29e5-4ec8-8442-9b404f66770d
-- title:
--   Prop. 2.2 remark: the gauge freedom of the recovered pair
-- statement:
--   Spacetime is $\mathbb R^4$ in a global chart (index 0 = time) with $t_a=dx^0$, $h^{ab}=\mathrm{diag}(0,1,1,1)$; a derivative operator is a smooth symmetric Christoffel field $\Gamma^a{}_{bc}$; curvature in Malament's convention $\xi^bR^a{}_{bcd}=-2\nabla_{[c}\nabla_{d]}\xi^a$, $R_{bc}=R^n{}_{bcn}$; $\tilde\Gamma=\Gamma+t_bt_c\nabla^a\varphi$ is the geometrization; timelike curves have unit tangent $t_a\xi^a=1$. If $(\nabla,\varphi)$ satisfies the conclusion of Prop. 2.2 for $(\tilde\nabla,\rho)$, then another pair $(\nabla',\varphi')$ does iff $\psi=\varphi'-\varphi$ satisfies $\nabla^a\nabla^b\psi=0$ and $\nabla'=(\nabla,t_bt_c\nabla^a\psi)$, i.e. $\Gamma'=\Gamma-t_bt_c\nabla^a\psi$.
-- source:
--   J. O. Weatherall, Are Newtonian Gravitation and Geometrized Newtonian Gravitation Theoretically Equivalent?, Erkenntnis 81 (2016) 1073-1091, https://arxiv.org/abs/1411.5757, remark after Prop. 2.2 (p. 5); used in App. A, proof of Prop. 6.1; D. B. Malament, Topics in the Foundations of General Relativity and Newtonian Gravitation Theory (2012), Ch. 4, Prop. 4.2.5 (uniqueness clause)

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- **Non-uniqueness in Prop. 2.2 (Weatherall p. 5; Malament Prop. 4.2.5).** If `(φ, ∇)` satisfies the
conclusion of Prop. 2.2 for `(∇̃, ρ)`, then a second pair `(φ', ∇')` satisfies the same conditions
iff `ψ = φ' - φ` obeys `∇^a ∇^b ψ = 0` and `∇' = (∇, t_b t_c ∇^a ψ)`. -/
theorem gauge_iff (Γt Γ Γ' : Conn) (φ φ' ρ : E → ℝ) (hΓt : IsClassical Γt)
    (hNG : IsNG Γ φ) (hT : SameTrajectories Γ φ Γt) (hP : Poisson Γ φ ρ) :
    (IsNG Γ' φ' ∧ SameTrajectories Γ' φ' Γt ∧ Poisson Γ' φ' ρ) ↔
      (IsGauge Γ (fun x => φ' x - φ x) ∧ Γ' = gaugeΓ Γ (fun x => φ' x - φ x)) := by sorry

end NewtonCartan
