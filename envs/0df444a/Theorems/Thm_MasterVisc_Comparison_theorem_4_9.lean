-- Prove2me | Theorems.Thm_MasterVisc_Comparison_theorem_4_9
-- name    : MasterVisc.Comparison.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:47:19.031991+00:00
-- url     : https://prove2.me/theorems/9653421f-e365-427d-84d7-d2fd79fe2064
-- title:
--   Theorem 4.9, pp. 961–962 — the change of variable Ṽ = e^{λt}V preserves L-viscosity (sub/super)solutions
-- statement:
--   Let $G$ satisfy Assumption 3.1, $V\in C^0(\Theta)$, $L>0$ and $\lambda\in\mathbb R$. Define
--   $$\tilde V(t,\mu)=e^{\lambda t}V(t,\mu),\qquad \tilde G(t,\mu,y,Z,\Gamma)=e^{\lambda t}G\big(t,\mu,e^{-\lambda t}y,e^{-\lambda t}Z,e^{-\lambda t}\Gamma\big).$$
--   Then $V$ is an $L$-viscosity solution (resp. subsolution, supersolution) of (3.1) if and only if $\tilde V$ is an $L$-viscosity solution (resp. subsolution, supersolution) of
--   $$\partial_t\tilde V(t,\mu)-\lambda\tilde V(t,\mu)+\tilde G\big(t,\mu,\tilde V,\partial_\mu\tilde V,\partial_\omega\partial_\mu\tilde V\big)=0.\qquad(4.10)$$
--
--   The transformation is used to assume, without loss of generality, that $G$ is monotone in $y$ in the comparison arguments (Theorem 4.11, Proposition 4.12).
--
--   **Formalization Note.** (4.10) is (3.1) with the generator $(t,\mu,y,Z,\Gamma)\mapsto-\lambda y+\tilde G(t,\mu,y,Z,\Gamma)$; the three equivalences are stated for the same $L$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Theorem 4.9, pp. 961–962, (4.10)

import Mathlib
import Definitions.Def_MasterVisc_Comparison_Setting
import Definitions.Def_MasterVisc_Comparison_Viscosity
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MasterVisc.Comparison

/-- Theorem 4.9, pp. 961–962: with `Ṽ(t, μ) = e^{λt}V(t, μ)` and
`G̃(t, μ, y, Z, Γ) = e^{λt}G(t, μ, e^{−λt}y, e^{−λt}Z, e^{−λt}Γ)`, `V` is an `L`-viscosity solution (resp.
subsolution, supersolution) of (3.1) iff `Ṽ` is one of (4.10), i.e. of (3.1) with generator `−λy + G̃`. -/
theorem theorem_4_9 {d : ℕ} {T : ℝ≥0} (L₀ : ℝ) (G : Gen d T) (hG : Assumption31 L₀ G)
    (V : ℝ≥0 → Measure (Path d T) → ℝ) (hV : IsC0Θ V) (L : ℝ) (hL : 0 < L) (lam : ℝ) :
    let Vt : ℝ≥0 → Measure (Path d T) → ℝ := fun t μ => Real.exp (lam * t) * V t μ
    let Gt : Gen d T := fun t μ y Z Γ =>
      -lam * y + Real.exp (lam * t) * G t μ (Real.exp (-lam * t) * y)
        (fun ω => Real.exp (-lam * t) • Z ω) (fun ω => Real.exp (-lam * t) • Γ ω)
    (IsLViscSol L G V ↔ IsLViscSol L Gt Vt) ∧
    (IsLViscSub L G V ↔ IsLViscSub L Gt Vt) ∧
    (IsLViscSuper L G V ↔ IsLViscSuper L Gt Vt) := by sorry

end MasterVisc.Comparison
