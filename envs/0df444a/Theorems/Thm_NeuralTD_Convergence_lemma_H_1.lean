-- Prove2me | Theorems.Thm_NeuralTD_Convergence_lemma_H_1
-- name    : NeuralTD.Convergence.lemma_H_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:15.620142+00:00
-- url     : https://prove2.me/theorems/4b786246-a490-43ed-9f8b-d41722cac261
-- title:
--   Lemma H.1, p. 57 — E_init,µ[(1/m)Σ_r 1{|W_r(0)ᵀx| ≤ ‖W_r − W_r(0)‖₂}] ≤ c1·B·m^{−1/2} for every random W with ‖W − W(0)‖₂ ≤ B
-- statement:
--   Let $d \ge 3$ and $c_0 > 0$. There is a constant $c_1 > 0$ such that the following holds for every width $m \ge 1$, radius $B \ge 0$ and sampling law $\mu$ satisfying Assumption 4.3 with constant $c_0$. Let $(b, W(0))$ be drawn from the initialization law, and let $W$ be any random parameter, defined on the same probability space together with an auxiliary source of randomness and independent of a fresh tuple $(x,r,x') \sim \mu$, with $\|W - W(0)\|_2 \le B$ always. Then
--   $$\mathbb E_{\mathrm{init},\mu}\Big[\frac1m\sum_{r=1}^m \mathbb 1\big\{|W_r(0)^\top x| \le \|W_r - W_r(0)\|_2\big\}\Big] \le c_1\, B\, m^{-1/2}.$$
--
--   The left-hand side bounds the expected fraction of hidden units whose activation pattern at $x$ can differ between $W(0)$ and $W$; it is the basic estimate behind every linearization error in the paper.
--
--   **Formalization Note.** "A random vector $W$" is a measurable map $W : (b, W(0), \omega) \mapsto W$ on the product of the initialization law with an arbitrary probability space $(\Xi,\nu)$; the fresh tuple is integrated innermost, so it is independent of $W$. The constant $c_1$ is chosen before $m$, $B$, $\mu$ and $W$, and depends only on $c_0$ and $d$ (the proof gives $c_0\sqrt{d/(d-2)}$). Expectations of nonnegative quantities are lower Lebesgue integrals.
-- source:
--   Cai, Yang, Lee, Wang, Neural temporal-difference and Q-learning provably converge to global optima, arXiv:1905.10027v2, p. 57, Lemma H.1

import Mathlib
import Definitions.Def_NeuralTD_Convergence_Setting

namespace NeuralTD.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- Lemma H.1 (p. 57): the expected fraction of neurons whose activation pattern can flip
within the ball is `O(B m^{−1/2})`, for every random `W` in `S_B` independent of the fresh `x`. -/
theorem lemma_H_1 (d : ℕ) (hd : 3 ≤ d) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (B : ℝ), 0 ≤ B → ∀ (rbar : ℝ) (μ : Measure (Sample d)),
      IsSamplingLaw d rbar μ → Assumption43 c0 μ →
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
        (W : Init m d × Ξ → Param m d), Measurable W → (∀ p, ‖W p - p.1.2‖ ≤ B) →
        ∫⁻ p, ∫⁻ ξ, ENNReal.ofReal ((m : ℝ)⁻¹ *
            ∑ r, (if |⟪p.1.2 r, ξ.1⟫| ≤ ‖W p r - p.1.2 r‖ then (1 : ℝ) else 0))
          ∂μ ∂((initLaw m d).prod ν)
          ≤ ENNReal.ofReal (c1 * B * (m : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end NeuralTD.Convergence
