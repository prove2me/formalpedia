-- Prove2me | Theorems.Thm_NonconvexSaddle_PGDVar_lemma_22
-- name    : NonconvexSaddle.PGDVar.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:11:12.599417+00:00
-- url     : https://prove2.me/theorems/a5992125-49d3-4804-bf83-179454208950
-- title:
--   Lemma 22 — coupling sequence: of two GD runs ηr₀ apart along e₁, one decreases f by ℱ within 𝒯 steps
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$, $d\ge1$, satisfy Assumption A with $\ell,\rho>0$, let $\varepsilon>0$ and $\iota\ge1$ with $\sqrt{\rho\varepsilon}\le\ell$, and use the parameters of Eq. (6): $\eta=1/\ell$, $r=\varepsilon/(400\iota^3)$, $\mathscr T=\ell\iota/\sqrt{\rho\varepsilon}$ (assumed to be an integer), $\mathscr F=\sqrt{\varepsilon^3/\rho}/(50\iota^3)$, $\mathscr S=\sqrt{\varepsilon/\rho}/(4\iota)$, and $\omega=2^{2-\iota}\ell\mathscr S$.
--
--   Let $\tilde x\in\mathbb R^d$ and suppose $\lambda_{\min}(\nabla^2 f(\tilde x))=-\gamma\le-\sqrt{\rho\varepsilon}$, with unit eigenvector $e_1$: $\nabla^2f(\tilde x)e_1=-\gamma e_1$, $\|e_1\|=1$. Let $\{x_t\}$, $\{x'_t\}$ be two gradient descent sequences (step size $\eta$) such that
--
--   1. $\max\{\|x_0-\tilde x\|,\|x'_0-\tilde x\|\}\le\eta r$, and
--   2. $x_0-x'_0=\eta r_0e_1$ with $r_0>\omega$.
--
--   Then
--   $$\min\{f(x_{\mathscr T})-f(x_0),\ f(x'_{\mathscr T})-f(x'_0)\}\le-\mathscr F .$$
--
--   Near a point with a direction of sufficiently negative curvature, the set of starting points from which gradient descent fails to decrease $f$ by $\mathscr F$ within $\mathscr T$ steps is thin along that direction: its width along $e_1$ is at most $\eta\omega$. This is the geometric core of Lemma 20.
--
--   **Formalization Note** "$e_1$ is the minimum eigenvector of $\nabla^2 f(\tilde x)$" is expressed by a number $\gamma$ with $\nabla^2f(\tilde x)e_1=-\gamma e_1$, $\|e_1\|=1$ and $\langle\nabla^2f(\tilde x)v,v\rangle\ge-\gamma\|v\|^2$ for all $v$, so $-\gamma$ is the smallest eigenvalue; the hypothesis $\lambda_{\min}\le-\sqrt{\rho\varepsilon}$ is $\sqrt{\rho\varepsilon}\le\gamma$. The time interval $\mathscr T$ is a natural number equal to $\ell\iota/\sqrt{\rho\varepsilon}$; the proof uses $x_{\mathscr T}$ and $2\eta\rho\mathscr S\mathscr T=1/2$ exactly, so no rounding is applied. $\iota\ge1$ and $\ell/\sqrt{\rho\varepsilon}\ge1$ (footnote 1, p. 14) are the standing assumptions of the §5 proofs. $2^{2-\iota}$ is a real power.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 14, Lemma 22 (parameters Eq. (6), p. 12; footnote 1, p. 14)

import Mathlib
import Definitions.Def_NonconvexSaddle_PGDVar_Setting

open scoped RealInnerProductSpace

namespace NonconvexSaddle.PGDVar

/-- Lemma 22 (Coupling Sequence), arXiv:1902.04811v2, p. 14, with the parameters of Eq. (6):
`η = 1/ℓ`, `r = ε/(400ι³)`, `𝒯 = ℓι/√(ρε)` (a natural number), `ℱ = √(ε³/ρ)/(50ι³)`,
`𝒮 = √(ε/ρ)/(4ι)` and `ω = 2^{2−ι}ℓ𝒮`, under the standing assumptions `ι ≥ 1` and `ℓ ≥ √(ρε)`
(footnote 1, p. 14). Let `f` satisfy Assumption A, let `e₁` be a unit eigenvector of `∇²f(x̃)` for its
smallest eigenvalue `−γ`, with `−γ ≤ −√(ρε)`. If two gradient descent sequences start at `x₀, x₀'`
with `‖x₀ − x̃‖, ‖x₀' − x̃‖ ≤ ηr` and `x₀ − x₀' = ηr₀e₁` with `r₀ > ω`, then
`min{f(x_𝒯) − f(x₀), f(x'_𝒯) − f(x₀')} ≤ −ℱ`. -/
theorem lemma_22 {d : ℕ} (hd : 1 ≤ d) (f : NonconvexSaddle.PSGD.E d → ℝ) (ℓ ρ ε ι : ℝ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hι : 1 ≤ ι) (hfoot : Real.sqrt (ρ * ε) ≤ ℓ) (hA : NonconvexSaddle.PSGD.AssumptionA f ℓ ρ)
    (𝒯 : ℕ) (h𝒯 : (𝒯 : ℝ) = timeInterval ℓ ρ ε ι)
    (xtil e₁ : NonconvexSaddle.PSGD.E d) (γ : ℝ) (hγ : Real.sqrt (ρ * ε) ≤ γ) (he₁ : ‖e₁‖ = 1)
    (heig : NonconvexSaddle.PSGD.hess f xtil e₁ = (-γ) • e₁)
    (hmin : ∀ v : NonconvexSaddle.PSGD.E d, -γ * ‖v‖ ^ 2 ≤ ⟪NonconvexSaddle.PSGD.hess f xtil v, v⟫)
    (x₀ x₀' : NonconvexSaddle.PSGD.E d) (r₀ : ℝ)
    (hx₀ : ‖x₀ - xtil‖ ≤ eta ℓ * radius ε ι) (hx₀' : ‖x₀' - xtil‖ ≤ eta ℓ * radius ε ι)
    (hdiff : x₀ - x₀' = (eta ℓ * r₀) • e₁) (hr₀ : omega ℓ ρ ε ι < r₀) :
    min (f ((gdStep f (eta ℓ))^[𝒯] x₀) - f x₀) (f ((gdStep f (eta ℓ))^[𝒯] x₀') - f x₀') ≤
      -decr ρ ε ι := by sorry

end NonconvexSaddle.PGDVar
