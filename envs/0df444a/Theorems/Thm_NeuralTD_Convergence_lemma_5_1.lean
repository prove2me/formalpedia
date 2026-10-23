-- Prove2me | Theorems.Thm_NeuralTD_Convergence_lemma_5_1
-- name    : NeuralTD.Convergence.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:17.945673+00:00
-- url     : https://prove2.me/theorems/957d7ec1-3046-479c-a87b-d93244e1146b
-- title:
--   Lemma 5.1, p. 12 — E_init,µ[|Q̂(x; W) − Q̂0(x; W)|²] ≤ 4c1B³m^{−1/2}, posed for every random W in S_B (covers W(t) and W̄)
-- statement:
--   Let $d \ge 3$ and $c_0 > 0$. There is a constant $c_1 > 0$ such that, for every width $m \ge 1$, radius $B \ge 0$, sampling law $\mu$ satisfying Assumption 4.3 with constant $c_0$, and every random parameter $W$ with $\|W - W(0)\|_2 \le B$ that is independent of a fresh $x \sim \mu$,
--   $$\mathbb E_{\mathrm{init},\mu}\Big[\big|\widehat Q(x; W) - \widehat Q_0(x; W)\big|^2\Big] \le 4 c_1 B^3\, m^{-1/2}.$$
--
--   The overparametrized network stays close to its linearization at initialization throughout the ball $S_B$: the error vanishes as the width $m \to \infty$.
--
--   **Formalization Note.** The paper states the lemma for the iterates $W = W(t)$, $t \in [T]$, of Algorithm 1. Its proof (Appendix C.1) uses only $\|W - W(0)\|_2 \le B$ and the independence of $W$ from the fresh $x$, and the proof of Theorem 4.4/4.6 applies it to the average $\overline W$ ((C.25)); the statement is therefore posed for every random $W$ in $S_B$ (modelled as in Lemma H.1), which contains the case $W = W(t)$ (take the run's sample sequence as the auxiliary randomness).
-- source:
--   Cai, Yang, Lee, Wang, Neural temporal-difference and Q-learning provably converge to global optima, arXiv:1905.10027v2, p. 12, Lemma 5.1 (proof: Appendix C.1, pp. 28–29)

import Mathlib
import Definitions.Def_NeuralTD_Convergence_Setting

namespace NeuralTD.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- Lemma 5.1 (p. 12): local linearization of the Q-function, posed for every random `W` in `S_B`
(independent of the fresh `x`); this covers every iterate `W(t)` and the average `W̄`. -/
theorem lemma_5_1 (d : ℕ) (hd : 3 ≤ d) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (B : ℝ), 0 ≤ B → ∀ (rbar : ℝ) (μ : Measure (Sample d)),
      IsSamplingLaw d rbar μ → Assumption43 c0 μ →
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
        (W : Init m d × Ξ → Param m d), Measurable W → (∀ p, ‖W p - p.1.2‖ ≤ B) →
        ∫⁻ p, ∫⁻ ξ, ENNReal.ofReal ((Qhat p.1.1 (W p) ξ.1 - Qlin p.1.1 p.1.2 (W p) ξ.1) ^ 2)
          ∂μ ∂((initLaw m d).prod ν)
          ≤ ENNReal.ofReal (4 * c1 * B ^ 3 * (m : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end NeuralTD.Convergence
