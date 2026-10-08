-- Prove2me | Theorems.Thm_LariviereIGFR_Char_failureRate_log_eq
-- name    : LariviereIGFR.Char.failureRate_log_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:35.55263+00:00
-- url     : https://prove2.me/theorems/c585803a-9a1d-4245-b725-da33466f0718
-- title:
--   Proof of Theorem 1, p. 603 — h_L(ξ) = g(e^ξ) and h′_L(ξ) = e^ξ g′(e^ξ)
-- statement:
--   Let $X \ge 0$ have law $\mu$ with regular density $\varphi$ and generalized failure rate $g(\xi) = \xi\varphi(\xi)/\bar\Phi(\xi)$, and let $h_L$ be the failure rate of $X_L = \log X$ computed with the density $\varphi_L(\xi) = e^{\xi}\varphi(e^{\xi})$. Then for every real $\xi$,
--   $$h_L(\xi) = g(e^{\xi}),$$
--   and whenever $g$ is differentiable at $e^{\xi}$, $h_L$ is differentiable at $\xi$ with
--   $$h_L'(\xi) = e^{\xi} g'(e^{\xi}).$$
--
--   The identity turns monotonicity of $g$ on $(0,\infty)$ into monotonicity of $h_L$ on $\mathbb R$; it is the computation behind the equivalence of parts 1 and 2 of Theorem 1.
--
--   **Formalization Note** The identity is stated at every $\xi$; where $\bar\Phi(e^\xi) = 0$ both sides are $0$ under Lean's convention $x/0 = 0$. The derivative clause does not assume $g$ differentiable anywhere: it is conditional on the existence of $g'(e^\xi)$, as in the paper.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §2, proof of Theorem 1, first sentence

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

namespace LariviereIGFR.Char

open MeasureTheory ProbabilityTheory

theorem failureRate_log_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    (∀ ξ : ℝ, failureRate (μ.map Real.log) (fun ξ => Real.exp ξ * φ (Real.exp ξ)) ξ =
        genFailureRate μ φ (Real.exp ξ)) ∧
      ∀ ξ d : ℝ, HasDerivAt (genFailureRate μ φ) d (Real.exp ξ) →
        HasDerivAt (failureRate (μ.map Real.log) (fun ξ => Real.exp ξ * φ (Real.exp ξ)))
          (Real.exp ξ * d) ξ := by sorry

end LariviereIGFR.Char
