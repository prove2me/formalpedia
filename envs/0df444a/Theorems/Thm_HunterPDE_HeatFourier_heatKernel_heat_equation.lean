-- Prove2me | Theorems.Thm_HunterPDE_HeatFourier_heatKernel_heat_equation
-- name    : HunterPDE.HeatFourier.heatKernel_heat_equation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:58:45.627563+00:00
-- url     : https://prove2.me/theorems/3c7f27fe-5e0f-4c2f-bb34-fff12000880a
-- title:
--   Eq. (5.9) — Γ is C^∞ on ℝⁿ × (0,∞) and Γ_t = ΔΓ for t > 0
-- statement:
--   The heat kernel $\Gamma(x,t) = (4\pi t)^{-n/2} e^{-|x|^2/4t}$ is an infinitely differentiable function of $(x,t)$ on $\mathbb{R}^n \times (0,\infty)$, and it solves the heat equation there:
--   $$\Gamma_t = \Delta \Gamma \qquad (t > 0).$$
--
--   **Formalization Note.** Smoothness is joint `ContDiffOn ℝ ∞` on $\mathbb{R}^n \times (0,\infty)$; $\Gamma_t$ is the derivative in $t$ at fixed $x$, and $\Delta$ is Mathlib's Laplacian in $x$ on the inner-product space `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 131, Eq. (5.9)

import Mathlib
import Definitions.Def_HunterPDE_HeatFourier_HeatKernel

namespace HunterPDE.HeatFourier

open scoped ContDiff Laplacian

/-- Hunter, *Notes on PDEs*, p. 131, Eq. (5.9): the heat kernel `Γ(x, t)` of (5.6) is a
`C^∞`-function of `(x, t)` in `ℝⁿ × (0, ∞)`, and `Γₜ = ΔΓ` if `t > 0`.
`Δ` is Mathlib's Laplacian in `x` on `EuclideanSpace ℝ (Fin n)` (the sum of the pure second
partial derivatives), `Γₜ` the ordinary derivative in `t` at fixed `x`. -/
theorem heatKernel_heat_equation (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) × ℝ => heatKernel n z.1 z.2)
      (Set.univ ×ˢ Set.Ioi 0) ∧
    ∀ (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
      deriv (fun s : ℝ => heatKernel n x s) t = Δ (fun y => heatKernel n y t) x := by sorry

end HunterPDE.HeatFourier
