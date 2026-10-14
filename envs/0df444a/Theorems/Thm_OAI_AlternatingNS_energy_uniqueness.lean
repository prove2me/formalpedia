-- Prove2me | Theorems.Thm_OAI_AlternatingNS_energy_uniqueness
-- name    : OAI.AlternatingNS.energy_uniqueness
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-12T01:25:50.489188+00:00
-- url     : https://prove2.me/theorems/ece489b9-a73f-4cc7-8797-e5ec1e39fc19
-- title:
--   Weak–strong uniqueness for the forced Navier–Stokes equation in the competitor energy class
-- statement:
--   Let $\nu>0$ and let $U$ be a smooth, compactly supported, rapidly decaying zero-pressure solution of the forced Navier–Stokes equation with force $f=\partial_tU+(U\cdot\nabla)U-\nu\Delta U$, lying in the energy class. Let $(v,p)$ be any classical solution with the same force and $v(0)=0$ such that, on every $[0,T]$, $v$ is continuous in $H^2$, continuously differentiable in $L^2$ and bounded, and $p$ is continuous in $H^1$. Then $v(t,x)=U(t,x)$ and $p(t,x)=0$ for all $t\ge0$ and $x\in\mathbb R^3$.
--
--   Proof idea: $w=v-U$ satisfies $\frac12\frac{d}{dt}\|w\|_2^2+\nu\|\nabla w\|_2^2=-\int(w\cdot\nabla)U\cdot w$, because the transport and pressure terms vanish after integration by parts using $\operatorname{div}v=\operatorname{div}w=0$. Hence $\frac{d}{dt}\|w\|_2^2\le2\|\nabla U\|_\infty\|w\|_2^2$ and $w=0$ by Gronwall. Then $\nabla p=0$, so $p(t,\cdot)$ is a constant lying in $L^2(\mathbb R^3)$, hence zero.
--
--   **Formalization Note** Fields are functions $\mathbb R\to\mathbb R^3\to E$ (`Field`); only $t\ge0$ matters. `Smooth` is $C^\infty$ on $[0,\infty)\times\mathbb R^3$, `Rapid` bounds $(1+t+\|x\|)^J\|\partial_t^l\partial_x^\alpha F\|$ for all $J,l,\alpha$, `SupportedIn F K` means $\operatorname{supp}F(t,\cdot)\subseteq K$ for $t\ge0$, `residual ν U` is $\partial_tU+(U\cdot\nabla)U-\nu\Delta U$, and time derivatives are taken within $[0,\infty)$. All notions are those of the published definition `NavierStokesAlternating`.
-- source:
--   OpenAI, "Computation under Rapidly Vanishing Navier–Stokes Forcing" (September 27, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf; goal theorem OAI.AlternatingNS.alternating of the mission "Computation under Rapidly Vanishing Navier–Stokes Forcing"; classical weak–strong (energy) uniqueness for Navier–Stokes, e.g. J. Serrin (1963), G. Prodi (1959)

import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **Weak–strong uniqueness.** Let `U` be a smooth, rapidly decaying, compactly supported
zero-pressure solution of the forced Navier–Stokes equation with `ν > 0` in the energy class.
Every classical solution `(v, p)` with the same force and zero initial velocity in the
competitor energy class coincides with `(U, 0)` for all `t ≥ 0`. -/
theorem energy_uniqueness (ν : ℝ) (hν : 0 < ν) (U : Velocity) (K : Set Space) (hK : IsCompact K)
    (hU : Smooth U) (hs : SupportedIn U K) (hr : Rapid U)
    (hNS : NavierStokes ν (residual ν U) U (fun _ _ => 0)) (hE : EnergyClass U (fun _ _ => 0))
    (v : Velocity) (p : Pressure) (hv : NavierStokes ν (residual ν U) v p)
    (hc : CompetitorEnergyClass v p) :
    ∀ t, 0 ≤ t → ∀ x, v t x = U t x ∧ p t x = 0 := by
  sorry

end AlternatingNS
end OAI
