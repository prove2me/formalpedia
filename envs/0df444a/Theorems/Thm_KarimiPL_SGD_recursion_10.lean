-- Prove2me | Theorems.Thm_KarimiPL_SGD_recursion_10
-- name    : KarimiPL.SGD.recursion_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:48.076194+00:00
-- url     : https://prove2.me/theorems/90dc0f2f-7225-45d6-8be9-d8ba2fba6e11
-- title:
--   (10), p. 7 — E[f(x_{k+1}) − f*] ≤ (1 − 2α_kμ) E[f(x_k) − f*] + LC²α_k²/2 along the SG run
-- statement:
--   Consider problem (7): component functions $f_i$ ($i\sim\nu$, a probability measure) with $f(x) = \mathbb E_i[f_i(x)]$, each $f_i$ differentiable, and unbiased gradients $\mathbb E_i[\nabla f_i(x)]=\nabla f(x)$. Assume $f$ is differentiable with $L$-Lipschitz gradient ($L>0$), has a global minimizer $x^*$ with $f^*=f(x^*)$, and satisfies the Polyak–Łojasiewicz inequality with constant $\mu>0$:
--   $$\tfrac12\|\nabla f(x)\|^2 \ge \mu\,(f(x)-f^*)\quad\text{for all }x.$$
--   Run SG (9), $x_{k+1}=x_k-\alpha_k\nabla f_{i_k}(x_k)$, from $x_0$ with i.i.d. indices $i_k\sim\nu$, and suppose that almost surely $\mathbb E_i[\|\nabla f_i(x_k)\|^2]\le C^2$ at every iterate. Then, for every $k$ with $\alpha_k\ge0$,
--   $$\mathbb E[f(x_{k+1})-f^*] \;\le\; (1-2\alpha_k\mu)\,\mathbb E[f(x_k)-f^*] + \frac{LC^2\alpha_k^2}{2}.$$
--
--   This is the recursion (10) from which both step-size schemes of Theorem 4 follow.
--
--   **Formalization Note** Expectations are lower Lebesgue integrals over the infinite product law of the index sequence, with values in $[0,\infty]$; the factor $1-2\alpha_k\mu$ is replaced by its positive part (it is nonnegative in both schemes of Theorem 4). The joint measurability of $(i,x)\mapsto\nabla f_i(x)$ is assumed so that the iterates are measurable functions of the sample path; differentiability of each $f_i$ and $\alpha_k\ge0$ (a step size) are implicit in the paper.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, proof of Theorem 4, display (10), p. 7

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_SGD_Model

namespace KarimiPL.SGD

open MeasureTheory

/-- Recursion (10) of the proof of Theorem 4 (p. 7), along the SG run with any step sizes:
`E[f(x_{k+1}) - f*] ≤ (1 - 2 α_k μ) E[f(x_k) - f*] + L C² α_k² / 2` whenever `α_k ≥ 0`. -/
theorem recursion_10 {d : ℕ} {I : Type*} [MeasurableSpace I]
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
    (α : ℕ → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (C : ℝ)
    (hC : SecondMomentAlongRun F ν α x0 C)
    (k : ℕ) (hαk : 0 ≤ α k) :
    expectedGap F ν α x0 f (f xstar) (k + 1)
      ≤ ENNReal.ofReal (1 - 2 * α k * μ) * expectedGap F ν α x0 f (f xstar) k
        + ENNReal.ofReal (L * C ^ 2 * α k ^ 2 / 2) := by sorry

end KarimiPL.SGD
