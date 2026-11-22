-- Prove2me | Theorems.Thm_KarimiPL_SGD_decreasing_step_rate
-- name    : KarimiPL.SGD.decreasing_step_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:48.332191+00:00
-- url     : https://prove2.me/theorems/8bfaeada-58dc-4f39-becb-c9d50a10d0c5
-- title:
--   Theorem 4, decreasing step (pp. 6–7) — α_k = (2k+1)/(2μ(k+1)²) gives E[f(x_k) − f*] ≤ LC²/(2kμ²)
-- statement:
--   Under the hypotheses of Theorem 4 — problem (7) with each $f_i$ differentiable and unbiased gradients, $f$ differentiable with $L$-Lipschitz gradient ($L>0$), a global minimizer $x^*$ with $f^* = f(x^*)$, and the PL inequality with constant $\mu>0$ — run SG (9) from $x_0$ with i.i.d. indices and the decreasing step sizes
--   $$\alpha_k = \frac{2k+1}{2\mu(k+1)^2}.$$
--   If almost surely $\mathbb E_i[\|\nabla f_i(x_k)\|^2]\le C^2$ at every iterate of this run, then for every $k\ge1$
--   $$\mathbb E[f(x_k)-f^*] \;\le\; \frac{LC^2}{2k\mu^2}.$$
--
--   This is the $O(1/k)$ rate of the first half of Theorem 4; it matches the rate of SG under strong convexity without assuming convexity.
--
--   **Formalization Note** The bound is stated for $k\ge1$ (at $k=0$ the right side is undefined). Expectations are lower Lebesgue integrals of the nonnegative gap. Joint measurability of $(i,x)\mapsto\nabla f_i(x)$ is an added regularity assumption.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Theorem 4 (first rate), p. 6; proof, paragraph "Decreasing step size", p. 7

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_SGD_Model

namespace KarimiPL.SGD

open MeasureTheory

/-- Theorem 4, decreasing step size (statement p. 6, proof p. 7): with
`α_k = (2k+1)/(2μ(k+1)²)`, `E[f(x_k) - f*] ≤ L C² / (2 k μ²)` for every `k ≥ 1`. -/
theorem decreasing_step_rate {d : ℕ} {I : Type*} [MeasurableSpace I]
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
    (hC : SecondMomentAlongRun F ν (decStep μ) x0 C) :
    ∀ k : ℕ, 1 ≤ k →
      expectedGap F ν (decStep μ) x0 f (f xstar) k
        ≤ ENNReal.ofReal (L * C ^ 2 / (2 * k * μ ^ 2)) := by sorry

end KarimiPL.SGD
