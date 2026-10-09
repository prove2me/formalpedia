-- Prove2me | Theorems.Thm_KarimiPL_SGD_sg_step_bound
-- name    : KarimiPL.SGD.sg_step_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:45.685281+00:00
-- url     : https://prove2.me/theorems/e77198a5-d94a-4b55-bb50-7b980cb6f586
-- title:
--   Proof of Theorem 4, p. 7 — one SG step: E[f(x − a∇f_i(x))] ≤ f(x) − a‖∇f(x)‖² + LC²a²/2
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable with $L$-Lipschitz gradient ($L>0$), and let $x^*$ be a global minimizer of $f$, $f^* = f(x^*)$. Let $(f_i)_{i\in I}$ be component functions with unbiased gradients for $f$ under a probability measure $\nu$, i.e. $\mathbb E_{i\sim\nu}[\nabla f_i(y)] = \nabla f(y)$ with $i\mapsto\nabla f_i(y)$ integrable, for every $y$.
--
--   Fix a point $x$ and a constant $C$ with $\mathbb E_{i\sim\nu}\big[\|\nabla f_i(x)\|^2\big]\le C^2$. Then for every real step $a$,
--   $$\mathbb E_{i\sim\nu}\big[f(x - a\nabla f_i(x))\big] - f^* \;\le\; f(x) - f^* - a\|\nabla f(x)\|^2 + \frac{LC^2a^2}{2}.$$
--
--   This is the first two lines of the expectation display in the proof of Theorem 4: one SG step from $x$ with step $a$ decreases $f$ in expectation by $a\|\nabla f(x)\|^2$ up to a variance term $LC^2a^2/2$.
--
--   **Formalization Note** The left side is the lower Lebesgue integral of the nonnegative quantity $f(x-a\nabla f_i(x)) - f^*$, so no integrability of $i\mapsto f(x-a\nabla f_i(x))$ is assumed. The second-moment bound is assumed at the single point $x$.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, proof of Theorem 4, first and second displays (lines 1–2 of the expectation display), p. 7

import Mathlib
import Definitions.Def_KarimiPL_SGD_Model

namespace KarimiPL.SGD

open MeasureTheory

/-- One-step bound in the proof of Theorem 4 (p. 7): for any point `x` at which the
second moment of the stochastic gradient is at most `C²`, and any step `a`,
`E_i[f(x - a ∇F_i(x))] - f* ≤ f(x) - f* - a ‖∇f(x)‖² + L C² a² / 2`. -/
theorem sg_step_bound {d : ℕ} {I : Type*} [MeasurableSpace I]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ y, f xstar ≤ f y)
    (hunb : IsUnbiasedGradient F ν f)
    (x : EuclideanSpace ℝ (Fin d)) (C : ℝ)
    (hCx : ∫⁻ i, ‖gradient (F i) x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (C ^ 2))
    (a : ℝ) :
    ∫⁻ i, ENNReal.ofReal (f (x - a • gradient (F i) x) - f xstar) ∂ν
      ≤ ENNReal.ofReal (f x - f xstar - a * ‖gradient f x‖ ^ 2 + L * C ^ 2 * a ^ 2 / 2) := by sorry

end KarimiPL.SGD
