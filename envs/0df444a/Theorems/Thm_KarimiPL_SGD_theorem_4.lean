-- Prove2me | Theorems.Thm_KarimiPL_SGD_theorem_4
-- name    : KarimiPL.SGD.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:53.216408+00:00
-- url     : https://prove2.me/theorems/38dd10b5-ebfc-4bae-af73-6650bfbbbfe8
-- title:
--   Theorem 4, p. 6 — SG under PL: E[f(x_k) − f*] ≤ LC²/(2kμ²) (decreasing steps) and ≤ (1 − 2μα)^k [f(x_0) − f*] + LC²α/(4μ) (constant α < 1/(2μ))
-- statement:
--   Consider problem (7): an index $i$ drawn from a probability measure $\nu$, component functions $f_i:\mathbb R^d\to\mathbb R$, each differentiable, and
--   $$f(x) = \mathbb E_{i\sim\nu}[f_i(x)],\qquad \mathbb E_{i\sim\nu}[\nabla f_i(x)] = \nabla f(x)\quad\text{for all }x.$$
--   Assume that $f$ is differentiable with $L$-Lipschitz gradient ($L>0$), that $f$ has a global minimizer $x^*$ (write $f^*=f(x^*)$), and that $f$ satisfies the Polyak–Łojasiewicz inequality with constant $\mu>0$, $\tfrac12\|\nabla f(x)\|^2\ge\mu(f(x)-f^*)$ for all $x$. Run the SG method (9),
--   $$x_{k+1} = x_k - \alpha_k\nabla f_{i_k}(x_k),$$
--   from $x_0$, with $i_0,i_1,\dots$ independent draws from $\nu$. Let $C$ be a real constant.
--
--   1. **Decreasing steps.** If $\alpha_k = \dfrac{2k+1}{2\mu(k+1)^2}$ and almost surely $\mathbb E_i[\|\nabla f_i(x_k)\|^2]\le C^2$ at every iterate of this run, then for every $k\ge1$
--   $$\mathbb E[f(x_k)-f^*]\le\frac{LC^2}{2k\mu^2}.$$
--   2. **Constant step.** If $\alpha_k=\alpha$ with $0<\alpha<\dfrac1{2\mu}$ and almost surely $\mathbb E_i[\|\nabla f_i(x_k)\|^2]\le C^2$ at every iterate of this run, then for every $k\ge0$
--   $$\mathbb E[f(x_k)-f^*]\le(1-2\mu\alpha)^k[f(x_0)-f^*]+\frac{LC^2\alpha}{4\mu}.$$
--
--   The theorem shows that plain SG attains the $O(1/k)$ rate known under strong convexity using only the PL inequality, and that with a constant step it converges linearly to a neighbourhood of the optimal value whose size is proportional to the step.
--
--   **Formalization Note** Expectations are lower Lebesgue integrals of the nonnegative gap $f(x_k)-f^*$ over the infinite product law of the indices. The second-moment bound is required only along the iterates (the paper's "for all $x_k$"); a bound at every point $x$ would, together with the PL inequality and the Lipschitz gradient, force $f$ to be constant. Added relative to the page: each $f_i$ is differentiable (implicit in $\nabla f_i$), $\alpha>0$ in the constant scheme (a step size), the rate in the decreasing scheme is stated for $k\ge1$, and $(i,x)\mapsto\nabla f_i(x)$ is jointly measurable. The paper's "each $f$ has an $L$-Lipschitz continuous gradient" is read as a condition on $f$, which is all the proof uses.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Theorem 4, p. 6 (proof p. 7)

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_SGD_Model

namespace KarimiPL.SGD

open MeasureTheory

/-- Theorem 4 (p. 6). For problem (7) with `f` having an `L`-Lipschitz gradient, a minimizer
`xstar`, and the PL inequality with constant `μ`, the SG method (9) with i.i.d. indices satisfies:
(decreasing steps) if `α_k = (2k+1)/(2μ(k+1)²)` and `E_i‖∇F_i(x_k)‖² ≤ C²` along the iterates,
then `E[f(x_k) - f*] ≤ L C²/(2kμ²)` for `k ≥ 1`;
(constant step) if `α_k = α₀` with `0 < α₀ < 1/(2μ)` and `E_i‖∇F_i(x_k)‖² ≤ C²` along the
iterates, then `E[f(x_k) - f*] ≤ (1 - 2μα₀)^k [f(x_0) - f*] + L C² α₀/(4μ)`. -/
theorem theorem_4 {d : ℕ} {I : Type*} [MeasurableSpace I]
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
    (x0 : EuclideanSpace ℝ (Fin d)) (C : ℝ) :
    (SecondMomentAlongRun F ν (decStep μ) x0 C →
      ∀ k : ℕ, 1 ≤ k →
        expectedGap F ν (decStep μ) x0 f (f xstar) k
          ≤ ENNReal.ofReal (L * C ^ 2 / (2 * k * μ ^ 2))) ∧
    (∀ α₀ : ℝ, 0 < α₀ → α₀ < 1 / (2 * μ) →
      SecondMomentAlongRun F ν (fun _ => α₀) x0 C →
      ∀ k : ℕ,
        expectedGap F ν (fun _ => α₀) x0 f (f xstar) k
          ≤ ENNReal.ofReal ((1 - 2 * μ * α₀) ^ k * (f x0 - f xstar)
              + L * C ^ 2 * α₀ / (4 * μ))) := by sorry

end KarimiPL.SGD
