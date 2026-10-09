-- Prove2me | Theorems.Thm_NonconvexSaddle_PGDVar_lemma_20
-- name    : NonconvexSaddle.PGDVar.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:11:05.611169+00:00
-- url     : https://prove2.me/theorems/662da2e6-11a5-4367-98a9-7ca50d8a9e94
-- title:
--   Lemma 20 — escaping saddle points: a uniform perturbation then 𝒯 GD steps decrease f by ℱ/2 w.h.p.
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$, $d\ge1$, satisfy Assumption A with $\ell,\rho>0$, let $\varepsilon>0$ and $\iota\ge1$ with $\sqrt{\rho\varepsilon}\le\ell$, and use the parameters of Eq. (6): $\eta=1/\ell$, $r=\varepsilon/(400\iota^3)$, $\mathscr T=\ell\iota/\sqrt{\rho\varepsilon}$ (assumed to be an integer) and $\mathscr F=\sqrt{\varepsilon^3/\rho}/(50\iota^3)$.
--
--   Let $\tilde x$ satisfy $\|\nabla f(\tilde x)\|\le\varepsilon$ and $\lambda_{\min}(\nabla^2 f(\tilde x))\le-\sqrt{\rho\varepsilon}$. Let $x_0=\tilde x+\eta\xi$ with $\xi\sim\mathrm{Uniform}(B_0(r))$, and let $x_{\mathscr T}$ be the $\mathscr T$-th gradient descent iterate (step size $\eta$) from $x_0$. Then
--   $$\mathbb P\Bigl(f(x_{\mathscr T})-f(\tilde x)\le-\frac{\mathscr F}{2}\Bigr)\ge1-\frac{\ell\sqrt d}{\sqrt{\rho\varepsilon}}\cdot\iota^22^{8-\iota}.$$
--
--   A random perturbation at an approximate saddle point, followed by $\mathscr T$ steps of gradient descent, decreases the function value by at least $\mathscr F/2$ with high probability. Theorem 18 applies this every time Algorithm 4 perturbs.
--
--   **Formalization Note** The statement bounds the probability of the failure event, $\mathbb P\bigl(f(x_{\mathscr T})-f(\tilde x)>-\mathscr F/2\bigr)\le\frac{\ell\sqrt d}{\sqrt{\rho\varepsilon}}\iota^22^{8-\iota}$, under the uniform law on the open ball (`ProbabilityTheory.cond volume (ball 0 r)`). For a set that is not known to be measurable this is the stronger form: it gives a measurable subset of the success event with probability at least the right-hand side above. $\lambda_{\min}(\nabla^2f(\tilde x))\le-\sqrt{\rho\varepsilon}$ is written as the existence of a unit vector $v$ with $\langle\nabla^2 f(\tilde x)v,v\rangle\le-\sqrt{\rho\varepsilon}$, which is equivalent for $d\ge1$. $\mathscr T$ is a natural number equal to $\ell\iota/\sqrt{\rho\varepsilon}$; $\iota\ge1$ and $\ell\ge\sqrt{\rho\varepsilon}$ are the standing assumptions of §5 (footnote 1, p. 14); $2^{8-\iota}$ is a real power. The perturbation is added ($\tilde x+\eta\xi$) as in Lemma 20, while Algorithm 4 subtracts it; the uniform law is symmetric.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 13, Lemma 20 (proof p. 15; parameters Eq. (6), p. 12; footnote 1, p. 14)

import Mathlib
import Definitions.Def_NonconvexSaddle_PGDVar_Setting

open scoped RealInnerProductSpace

namespace NonconvexSaddle.PGDVar

/-- Lemma 20 (Escaping Saddle Points), arXiv:1902.04811v2, p. 13, with the parameters of Eq. (6)
(`η = 1/ℓ`, `r = ε/(400ι³)`, `𝒯 = ℓι/√(ρε)` a natural number, `ℱ = √(ε³/ρ)/(50ι³)`) and the standing
assumptions `ι ≥ 1`, `ℓ ≥ √(ρε)` (footnote 1, p. 14): if `f` satisfies Assumption A, `‖∇f(x̃)‖ ≤ ε` and
`λ_min(∇²f(x̃)) ≤ −√(ρε)`, and `x₀ = x̃ + ηξ` with `ξ ∼ Uniform(B₀(r))`, then the `𝒯`-th gradient
descent iterate from `x₀` satisfies `f(x_𝒯) − f(x̃) ≤ −ℱ/2` except on an event of probability at most
`ℓ√d/√(ρε) · ι² 2^{8−ι}`. -/
theorem lemma_20 {d : ℕ} (hd : 1 ≤ d) (f : NonconvexSaddle.PSGD.E d → ℝ) (ℓ ρ ε ι : ℝ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hι : 1 ≤ ι) (hfoot : Real.sqrt (ρ * ε) ≤ ℓ) (hA : NonconvexSaddle.PSGD.AssumptionA f ℓ ρ)
    (𝒯 : ℕ) (h𝒯 : (𝒯 : ℝ) = timeInterval ℓ ρ ε ι)
    (xtil : NonconvexSaddle.PSGD.E d) (hgrad : ‖gradient f xtil‖ ≤ ε)
    (hcurv : ∃ v : NonconvexSaddle.PSGD.E d, ‖v‖ = 1 ∧ ⟪NonconvexSaddle.PSGD.hess f xtil v, v⟫ ≤ -Real.sqrt (ρ * ε)) :
    uniformBall d (radius ε ι)
        {ξ : NonconvexSaddle.PSGD.E d | ¬ (f ((gdStep f (eta ℓ))^[𝒯] (xtil + eta ℓ • ξ)) - f xtil ≤ -decr ρ ε ι / 2)} ≤
      ENNReal.ofReal (ℓ * Real.sqrt d / Real.sqrt (ρ * ε) * ι ^ 2 * (2 : ℝ) ^ (8 - ι)) := by sorry

end NonconvexSaddle.PGDVar
