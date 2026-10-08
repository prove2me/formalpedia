-- Prove2me | Theorems.Thm_LariviereIGFR_Char_genFailureRate_scale
-- name    : LariviereIGFR.Char.genFailureRate_scale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:07.137169+00:00
-- url     : https://prove2.me/theorems/d7593e03-ee44-4143-9caf-372fac01fd98
-- title:
--   Proof of Theorem 1, p. 603 — the generalized failure rate of λX is g_λ(ξ) = g(ξ/λ)
-- statement:
--   Let $X \ge 0$ have law $\mu$ with distribution function $\Phi$ and regular density $\varphi$, and let $\lambda > 0$. Then $\lambda X$ has distribution function $\Phi_\lambda(\xi) = \Phi(\xi/\lambda)$, the function $\varphi_\lambda(\xi) = \varphi(\xi/\lambda)/\lambda$ is a regular density of $\lambda X$, and the generalized failure rate of $\lambda X$ computed with it satisfies, for every real $\xi$,
--   $$g_\lambda(\xi) = g(\xi/\lambda).$$
--
--   Scaling a random variable only rescales the argument of its generalized failure rate. This identity links parts 1 and 3 of Theorem 1.
--
--   **Formalization Note** $\lambda X$ is the image of $\mu$ under the measurable map $x \mapsto \lambda x$ (written `c` in Lean, since `λ` is reserved). The identity holds at every $\xi$, including where $\bar\Phi(\xi/\lambda) = 0$, where both sides are $0$ under Lean's convention $x/0 = 0$.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §2, proof of Theorem 1 ("the generalized failure rate of λX is g_λ(ξ) = g(ξ/λ)")

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

namespace LariviereIGFR.Char

open MeasureTheory ProbabilityTheory

theorem genFailureRate_scale (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ)
    (c : ℝ) (hc : 0 < c) :
    (∀ ξ : ℝ, cdf (μ.map (fun x => c * x)) ξ = cdf μ (ξ / c)) ∧
      IsRegDensity (μ.map (fun x => c * x)) (fun ξ => φ (ξ / c) / c) ∧
      ∀ ξ : ℝ, genFailureRate (μ.map (fun x => c * x)) (fun ξ => φ (ξ / c) / c) ξ =
        genFailureRate μ φ (ξ / c) := by sorry

end LariviereIGFR.Char
