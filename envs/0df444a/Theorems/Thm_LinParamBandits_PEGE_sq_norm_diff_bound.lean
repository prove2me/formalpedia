-- Prove2me | Theorems.Thm_LinParamBandits_PEGE_sq_norm_diff_bound
-- name    : LinParamBandits.PEGE.sq_norm_diff_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:20.911341+00:00
-- url     : https://prove2.me/theorems/d5c6fa7b-b445-460c-ae96-f900911018e6
-- title:
--   Lemma 3.4 — E[‖Ẑ(c) − z‖² | Z = z] ≤ h₁ r / c
-- statement:
--   Under Assumption 1 with constants $\sigma_0, \bar u, \lambda_0 > 0$, there is a constant $h_1 > 0$, depending only on $\sigma_0, \bar u, \lambda_0$, such that for every dimension $r \ge 2$, every arm set, error laws and exploration arms $b_1, \dots, b_r$ satisfying Assumption 1, every $z \in \mathbb R^r$ and every cycle $c \ge 1$,
--   $$\mathbb E\Big[\big\|\widehat Z(c) - z\big\|^2 \,\Big|\, Z = z\Big] \le \frac{h_1 r}{c},$$
--   where $\widehat Z(c)$ is the least squares estimate of PEGE after the exploration phase of cycle $c$.
--
--   The mean squared error of the estimate grows linearly with the dimension and decays as $1/c$; this rate is the source of the $r\sqrt T$ bound of Theorem 3.1.
--
--   **Formalization Note** The constant $h_1$ is chosen before $r$ and the instance. The expectation is a lower Lebesgue integral of the nonnegative squared error over the exploration errors, with the parameter fixed to $z$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma 3.4, p. 16

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Lemma 3.4 (Bound on Squared Norm Difference), Rusmevichientong, Tsitsiklis,
arXiv:0812.3465v2, p. 16: under Assumption 1 there is a positive constant `h₁`, depending only on
`σ₀, ū, λ₀`, such that for any `z ∈ ℝ^r` and `c ≥ 1`, `E[‖Ẑ(c) − z‖² | Z = z] ≤ h₁ r / c`. -/
theorem sq_norm_diff_bound (σ₀ ū lam₀ : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀) :
    ∃ h₁ : ℝ, 0 < h₁ ∧
      ∀ (r : ℕ), 2 ≤ r →
      ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r),
      Assumption1 𝒰 ν b σ₀ ū lam₀ →
      ∀ (z : LinParamBandits.LowerBound.Vec r) (c : ℕ), 1 ≤ c →
        ∫⁻ w, ENNReal.ofReal (‖Zhat b z w c - z‖ ^ 2) ∂(noiseLaw ν b)
          ≤ ENNReal.ofReal (h₁ * r / c) := by sorry
end LinParamBandits.PEGE
