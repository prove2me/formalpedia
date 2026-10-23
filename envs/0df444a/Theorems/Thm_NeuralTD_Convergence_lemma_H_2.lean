-- Prove2me | Theorems.Thm_NeuralTD_Convergence_lemma_H_2
-- name    : NeuralTD.Convergence.lemma_H_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:15.066568+00:00
-- url     : https://prove2.me/theorems/ac35c099-3d70-482e-88aa-6acf2961a351
-- title:
--   Lemma H.2, p. 58 — E_init[E_µ[Q̂0(x)²]·E_µ[(1/m)Σ_r 1{|W_r(0)ᵀx| ≤ ‖W_r − W_r(0)‖₂}]] ≤ c2·B·m^{−1/2} for every random W in S_B
-- statement:
--   Let $d \ge 3$ and $c_0 > 0$. There is a constant $c_2 > 0$ such that, for every width $m \ge 1$, radius $B \ge 0$, sampling law $\mu$ satisfying Assumption 4.3 with constant $c_0$, and every random parameter $W$ with $\|W - W(0)\|_2 \le B$ (as in Lemma H.1),
--   $$\mathbb E_{\mathrm{init}}\Big[\mathbb E_\mu\big[\widehat Q_0(x)^2\big]\cdot \mathbb E_\mu\Big[\frac1m\sum_{r=1}^m \mathbb 1\big\{|W_r(0)^\top x| \le \|W_r - W_r(0)\|_2\big\}\Big]\Big] \le c_2\, B\, m^{-1/2},$$
--   where $\widehat Q_0(x) = \widehat Q(x; W(0))$ is the network at initialization and both inner expectations are over a fresh $x \sim \mu$ for fixed $(b, W(0), W)$.
--
--   This controls the product of the size of the initial network and the fraction of flipping units; it enters the linearization error of the semigradient (Lemma 5.2).
--
--   **Formalization Note.** Random parameters are modelled as in Lemma H.1; the inner expectations are Bochner integrals of functions that are bounded $\mu$-almost surely (because $\|x\|_2 = 1$), hence integrable. The constant $c_2$ is chosen before $m$, $B$, $\mu$ and $W$.
-- source:
--   Cai, Yang, Lee, Wang, Neural temporal-difference and Q-learning provably converge to global optima, arXiv:1905.10027v2, p. 58, Lemma H.2

import Mathlib
import Definitions.Def_NeuralTD_Convergence_Setting

namespace NeuralTD.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- Lemma H.2 (p. 58): `E_init[E_μ[Q̂₀(x)²] · E_μ[(1/m) ∑_r 1{|W_r(0)ᵀx| ≤ ‖W_r − W_r(0)‖₂}]] ≤ c₂ B m^{−1/2}`. -/
theorem lemma_H_2 (d : ℕ) (hd : 3 ≤ d) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c2 : ℝ, 0 < c2 ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (B : ℝ), 0 ≤ B → ∀ (rbar : ℝ) (μ : Measure (Sample d)),
      IsSamplingLaw d rbar μ → Assumption43 c0 μ →
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
        (W : Init m d × Ξ → Param m d), Measurable W → (∀ p, ‖W p - p.1.2‖ ≤ B) →
        ∫⁻ p, ENNReal.ofReal ((∫ ξ, Qhat p.1.1 p.1.2 ξ.1 ^ 2 ∂μ) *
            (∫ ξ, (m : ℝ)⁻¹ *
              ∑ r, (if |⟪p.1.2 r, ξ.1⟫| ≤ ‖W p r - p.1.2 r‖ then (1 : ℝ) else 0) ∂μ))
          ∂((initLaw m d).prod ν)
          ≤ ENNReal.ofReal (c2 * B * (m : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end NeuralTD.Convergence
