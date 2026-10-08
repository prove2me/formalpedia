-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_fluid_eq_22
-- name    : MaxPressure.FluidStab.fluid_eq_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:54:41.111733+00:00
-- url     : https://prove2.me/theorems/3ca2026b-7856-4f80-8780-e6e1844b7def
-- title:
--   (22)–(23), p. 203 — Z̄(t) = Z̄(0) − RT̄(t) and ḟ(t) = 2Ż̄(t)·Z̄(t) = −2RṪ(t)·Z̄(t)
-- statement:
--   Let $(\bar Z,\bar T)$ be a fluid model solution, i.e. it satisfies (14)–(18). Then
--
--   1. the vector form (23) of (14) holds: $\bar Z(t)=\bar Z(0)-R\bar T(t)$ for every $t\ge0$;
--   2. at every regular time $t$, the quadratic Lyapunov function $f(t)=\sum_i\bar Z_i^2(t)$ of (21) is differentiable and
--   $$\dot f(t)=2\dot{\bar Z}(t)\cdot\bar Z(t)=-2R\dot{\bar T}(t)\cdot\bar Z(t).\qquad(22)$$
--
--   This identity holds under any service policy. Together with the maximum pressure equation (20) it shows that a maximum pressure policy makes the "system energy" $f$ decrease as fast as possible at every regular time.
--
--   **Formalization Note** A regular time is $t>0$ at which both $\bar Z$ and $\bar T$ are differentiable; $\dot{\bar Z}(t)$ and $\dot{\bar T}(t)$ are the derivatives there. $R\dot{\bar T}(t)\cdot\bar Z(t)$ is the pressure $p(\dot{\bar T}(t),\bar Z(t))$.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 203, (21)–(23)

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

namespace MaxPressure.FluidStab

open Matrix

/-- (22) and (23), §5, p. 203: for a fluid model solution, (14) in vector form is
`Z̄(t) = Z̄(0) − R T̄(t)` (23), and at a regular time `t` the Lyapunov function
`f(t) = ∑_i Z̄_i(t)²` (21) satisfies `ḟ(t) = 2 Ż̄(t) · Z̄(t) = −2 R Ṫ(t) · Z̄(t)` (22). -/
theorem fluid_eq_22 {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    (∀ s, 0 ≤ s → Zb s = Zb 0 - R N *ᵥ Tb s) ∧
    ∀ t, IsRegular Zb Tb t →
      HasDerivAt (fun s => ∑ i, Zb s i ^ 2) (2 * (deriv Zb t ⬝ᵥ Zb t)) t ∧
      2 * (deriv Zb t ⬝ᵥ Zb t) = -2 * pressure N (deriv Tb t) (Zb t) := by sorry

end MaxPressure.FluidStab
