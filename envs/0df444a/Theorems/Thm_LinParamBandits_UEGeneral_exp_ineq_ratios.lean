-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_exp_ineq_ratios
-- name    : LinParamBandits.UEGeneral.exp_ineq_ratios
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:13.293882+00:00
-- url     : https://prove2.me/theorems/2b6c68bb-5e36-44a6-815e-143bdc447a90
-- title:
--   Lemma B.3 — exponential inequality for ratios (De la Peña, Klass and Lai 2004)
-- statement:
--   Let $A$ and $B$ be random variables on a probability space such that $B \ge 0$ almost surely and
--   $$\mathbb E\big[e^{\gamma A - \gamma^2B^2/2}\big] \le 1 \qquad \text{for all } \gamma \in \mathbb R.$$
--   Then for all $\zeta \ge \sqrt 2$ and $y > 0$,
--   $$\Pr\left\{|A| \ge \zeta\sqrt{(B^2 + y)\Big(1 + \frac12\log\Big(1 + \frac{B^2}{y}\Big)\Big)}\right\} \le e^{-\zeta^2/2}.$$
--
--   This self-normalized tail bound is quoted by the paper from Corollary 2.2 of De la Peña, Klass and Lai (2004); it is the probabilistic input of the martingale inequality, Lemma B.4.
--
--   **Formalization Note** The expectation in the hypothesis is a lower Lebesgue integral of the nonnegative integrand, so the hypothesis cannot hold by a junk value of a non-integrable Bochner integral. $A$ and $B$ are measurable (they are random variables).
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma B.3, p. 30 (citing De la Peña, Klass, Lai 2004, Ann. Probab. 32, Corollary 2.2, p. 1908)

import Mathlib

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Lemma B.3 (p. 30; De la Peña, Klass and Lai 2004, Corollary 2.2): exponential inequality
for ratios. -/
theorem exp_ineq_ratios {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B) (hB0 : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hexp : ∀ γ : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * A ω - γ ^ 2 * B ω ^ 2 / 2)) ∂P ≤ 1)
    (ζ : ℝ) (hζ : Real.sqrt 2 ≤ ζ) (y : ℝ) (hy : 0 < y) :
    P {ω | ζ * Real.sqrt ((B ω ^ 2 + y) * (1 + 1 / 2 * Real.log (1 + B ω ^ 2 / y))) ≤ |A ω|} ≤
      ENNReal.ofReal (Real.exp (-ζ ^ 2 / 2)) := by sorry

end LinParamBandits.UEGeneral
