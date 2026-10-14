-- Prove2me | Theorems.Thm_OAI_AlternatingNS_zero_pressure_solution
-- name    : OAI.AlternatingNS.zero_pressure_solution
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-12T01:24:56.665034+00:00
-- url     : https://prove2.me/theorems/f13897c8-bd22-486f-b1d2-db9b4399aa82
-- title:
--   A smooth compactly supported divergence-free velocity from rest solves forced Navier–Stokes with zero pressure and lies in the energy class
-- statement:
--   Let $\nu\in\mathbb R$, $K\subset\mathbb R^3$ compact, and let $U$ be smooth on $[0,\infty)\times\mathbb R^3$, spatially supported in $K$, rapidly decaying, with $U(0,\cdot)=0$ and $\operatorname{div}U=0$. Then $(U,0)$ is a classical solution of
--   $$\partial_tU+(U\cdot\nabla)U=-\nabla p+\nu\Delta U+f,\qquad \operatorname{div}U=0,\qquad U(0)=0,$$
--   with $p=0$ and $f=\partial_tU+(U\cdot\nabla)U-\nu\Delta U$. Moreover, on every interval $[0,T]$, $U$ is continuous in $H^2$ and continuously differentiable in $L^2$, and $U$ and its spatial derivative are bounded.
--
--   The equation holds by the definition of $f$. The regularity follows from smoothness and compact support: spatial derivatives up to order two are continuous, compactly supported functions of $(t,x)$, hence continuous in $L^2$, and difference quotients in time converge uniformly on $[0,T]\times K$.
--
--   **Formalization Note** Fields are functions $\mathbb R\to\mathbb R^3\to E$ (`Field`); only $t\ge0$ matters. `Smooth` is $C^\infty$ on $[0,\infty)\times\mathbb R^3$, `Rapid` bounds $(1+t+\|x\|)^J\|\partial_t^l\partial_x^\alpha F\|$ for all $J,l,\alpha$, `SupportedIn F K` means $\operatorname{supp}F(t,\cdot)\subseteq K$ for $t\ge0$, `residual ν U` is $\partial_tU+(U\cdot\nabla)U-\nu\Delta U$, and time derivatives are taken within $[0,\infty)$. All notions are those of the published definition `NavierStokesAlternating`.
-- source:
--   OpenAI, "Computation under Rapidly Vanishing Navier–Stokes Forcing" (September 27, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf; goal theorem OAI.AlternatingNS.alternating of the mission "Computation under Rapidly Vanishing Navier–Stokes Forcing"

import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **Zero-pressure classical solution in the energy class.** A smooth, rapidly decaying,
compactly supported, divergence-free velocity field starting from rest solves the forced
Navier–Stokes equation with zero pressure and force `f = ∂ₜU + (U·∇)U − νΔU`, and lies in the
energy class. -/
theorem zero_pressure_solution (ν : ℝ) (U : Velocity) (K : Set Space) (hK : IsCompact K)
    (hU : Smooth U) (hs : SupportedIn U K) (hr : Rapid U) (h0 : ∀ x, U 0 x = 0)
    (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    NavierStokes ν (residual ν U) U (fun _ _ => 0) ∧ EnergyClass U (fun _ _ => 0) := by
  sorry

end AlternatingNS
end OAI
