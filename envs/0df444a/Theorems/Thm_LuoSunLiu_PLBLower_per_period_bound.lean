-- Prove2me | Theorems.Thm_LuoSunLiu_PLBLower_per_period_bound
-- name    : LuoSunLiu.PLBLower.per_period_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:15.495895+00:00
-- url     : https://prove2.me/theorems/78ae3ea2-d06e-46bf-b8fa-391d4b621ced
-- title:
--   Proof of Proposition 2, pp. 45–46 — with ξ_t = ξ_u iff P(A_t = U) ≥ 1/2, the expected one-period regret is ≥ C₀C_p, C₀ = 1/(4v)
-- statement:
--   Let $\tilde\xi\in\mathbb R^d$ have positive entries, let $j_u\neq j_v$ be two coordinates with $u=\tilde\xi_{j_u}\le v=\tilde\xi_{j_v}$, and let $0\le C<u$. Let $U,V,\xi_u,\xi_v$ be the two-point construction. Let $(\Omega,P)$ be a probability space and $A$ a measurable random action taking only the values $U$ and $V$ (the action of one period). The adversary sets
--   $$\xi_t=\begin{cases}\xi_u,& P(A=U)\ge 1/2,\\ \xi_v,& P(A=U)<1/2.\end{cases}$$
--   Then the expected one-period regret satisfies
--   $$\mathbb E\Big[\max\big(\langle\xi_t,U\rangle,\langle\xi_t,V\rangle\big)-\langle\xi_t,A\rangle\Big]\ \ge\ C_0C_p,\qquad C_0=\frac{1}{4v},\quad C_p=2C.$$
--
--   Summed over the periods $t=1,\dots,T_0$, with the action sets all equal to $\{U,V\}$ and $\xi_t$ chosen from the law of $A_t$ in each period, this gives the lower bound $C_0C_pT_0$ of Proposition 2.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral of the (nonnegative) regret. The choice of $\xi_t$ depends on the number $P(A=U)$, not on the realization, so $\xi_t$ is deterministic. The hypothesis $0\le C$ is the nonnegativity of the perturbation constant.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, App. A, proof of Proposition 2, pp. 45–46

import Mathlib
import Definitions.Def_LuoSunLiu_PLBLower_Model
import Definitions.Def_LuoSunLiu_PLBLower_TwoPoint

open MeasureTheory

namespace LuoSunLiu.PLBLower

/-- Per-period bound (proof of Proposition 2, pp. 45–46). Let the period-`t` action `A` be any
measurable random action with values in `{U, V}`, and let the adversary choose `ξ_t = ξ_u` if
`P(A = U) ≥ 1/2` and `ξ_t = ξ_v` otherwise. If `u ≤ v` (`u = ξ̃_{ju}`, `v = ξ̃_{jv}`) and
`0 ≤ C < u`, then the expected one-period regret
`E(r_t) = E(max(⟨ξ_t, U⟩, ⟨ξ_t, V⟩) − ⟨ξ_t, A⟩)` is at least `C_0 C_p` with `C_0 = 1/(4v)` and
`C_p = 2C`. -/
theorem per_period_bound {d : ℕ} (ξc : Fin d → ℝ) (hpos : ∀ i, 0 < ξc i)
    (C : ℝ) (hC0 : 0 ≤ C) (ju jv : Fin d) (hne : ju ≠ jv)
    (hCu : C < ξc ju) (huv : ξc ju ≤ ξc jv)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → Fin d → ℝ) (hA : Measurable A)
    (hAUV : ∀ ω, A ω = actU ξc C ju ∨ A ω = actV ξc C jv) :
    let ξ : Fin d → ℝ :=
      if (1 / 2 : ENNReal) ≤ P {ω | A ω = actU ξc C ju} then xiU ξc C ju jv
      else xiV ξc C ju jv
    ENNReal.ofReal (1 / (4 * ξc jv) * (2 * C)) ≤
      ∫⁻ ω, ENNReal.ofReal
        (max (ξ ⬝ᵥ actU ξc C ju) (ξ ⬝ᵥ actV ξc C jv) - ξ ⬝ᵥ A ω) ∂P := by sorry

end LuoSunLiu.PLBLower
