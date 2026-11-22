-- Prove2me | Theorems.Thm_KarimiPL_SGD_constant_step_rate
-- name    : KarimiPL.SGD.constant_step_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:11.772997+00:00
-- url     : https://prove2.me/theorems/cf1313b9-6682-4d18-8b2c-e1ad5c74e8cb
-- title:
--   Theorem 4, constant step (pp. 6–7) — α_k = α < 1/(2μ) gives E[f(x_k) − f*] ≤ (1 − 2μα)^k [f(x_0) − f*] + LC²α/(4μ)
-- statement:
--   Under the hypotheses of Theorem 4 — problem (7) with each $f_i$ differentiable and unbiased gradients, $f$ differentiable with $L$-Lipschitz gradient ($L>0$), a global minimizer $x^*$ with $f^* = f(x^*)$, and the PL inequality with constant $\mu>0$ — run SG (9) from $x_0$ with i.i.d. indices and a constant step size $\alpha_k=\alpha$, where
--   $$0<\alpha<\frac{1}{2\mu}.$$
--   If almost surely $\mathbb E_i[\|\nabla f_i(x_k)\|^2]\le C^2$ at every iterate of this run, then for every $k\ge0$
--   $$\mathbb E[f(x_k)-f^*] \;\le\; (1-2\mu\alpha)^k\,[f(x_0)-f^*] + \frac{LC^2\alpha}{4\mu}.$$
--
--   This is the second half of Theorem 4: linear convergence up to a noise floor proportional to the step size, so halving the step at least halves the floor.
--
--   **Formalization Note** The step size is required to be positive, which the paper leaves implicit. Expectations are lower Lebesgue integrals of the nonnegative gap. Joint measurability of $(i,x)\mapsto\nabla f_i(x)$ is an added regularity assumption.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Theorem 4 (second rate), p. 6; proof, paragraph "Constant step size", p. 7

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_SGD_Model

namespace KarimiPL.SGD

open MeasureTheory

/-- Theorem 4, constant step size (statement p. 6, proof p. 7): with `α_k = α₀` for a
step `0 < α₀ < 1/(2μ)`,
`E[f(x_k) - f*] ≤ (1 - 2μα₀)^k [f(x_0) - f*] + L C² α₀ / (4μ)` for every `k`. -/
theorem constant_step_rate {d : ℕ} {I : Type*} [MeasurableSpace I]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ y, f xstar ≤ f y)
    (μ : ℝ) (hμ : 0 < μ) (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar))
    (hf : IsStochObjective F ν f)
    (hFdiff : ∀ i, Differentiable ℝ (F i))
    (hunb : IsUnbiasedGradient F ν f)
    (hmeas : Measurable (fun p : I × EuclideanSpace ℝ (Fin d) => gradient (F p.1) p.2))
    (x0 : EuclideanSpace ℝ (Fin d)) (C : ℝ)
    (α₀ : ℝ) (hα₀pos : 0 < α₀) (hα₀ : α₀ < 1 / (2 * μ))
    (hC : SecondMomentAlongRun F ν (fun _ => α₀) x0 C) :
    ∀ k : ℕ,
      expectedGap F ν (fun _ => α₀) x0 f (f xstar) k
        ≤ ENNReal.ofReal ((1 - 2 * μ * α₀) ^ k * (f x0 - f xstar)
            + L * C ^ 2 * α₀ / (4 * μ)) := by sorry

end KarimiPL.SGD
