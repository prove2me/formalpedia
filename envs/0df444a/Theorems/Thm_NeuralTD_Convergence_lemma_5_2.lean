-- Prove2me | Theorems.Thm_NeuralTD_Convergence_lemma_5_2
-- name    : NeuralTD.Convergence.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:19.311037+00:00
-- url     : https://prove2.me/theorems/0e3b2bd4-2c8a-4a41-847e-0a7834b4c266
-- title:
--   Lemma 5.2, p. 12 — E_init[‖ḡ(W) − ḡ0(W)‖²₂] ≤ (56c1B³ + 24c2B + 6c1Br̄²)·m^{−1/2}, posed for every random W in S_B
-- statement:
--   Let $d \ge 3$ and $c_0 > 0$. There are constants $c_1, c_2 > 0$, depending only on $c_0$ and $d$, such that for every width $m \ge 1$, radius $B \ge 0$, reward bound $\bar r \ge 0$, discount $0 \le \gamma < 1$, sampling law $\mu$ with reward bound $\bar r$ satisfying Assumption 4.3 with constant $c_0$, and every random parameter $W$ with $\|W - W(0)\|_2 \le B$,
--   $$\mathbb E_{\mathrm{init}}\Big[\big\|\bar g(W) - \bar g_0(W)\big\|_2^2\Big] \le \big(56 c_1 B^3 + 24 c_2 B + 6 c_1 B \bar r^2\big)\, m^{-1/2},$$
--   where $\bar g(W) = \mathbb E_\mu[\delta(x,r,x';W)\nabla_W\widehat Q(x;W)]$ is the population semigradient and $\bar g_0(W) = \mathbb E_\mu[\delta_0(x,r,x';W)\nabla_W\widehat Q_0(x;W)]$ its linearized version.
--
--   This transfers the linearization error of Lemma 5.1 to the update direction of TD: the population semigradient is close to that of the linear TD problem defined by $\widehat Q_0$.
--
--   **Formalization Note.** As for Lemma 5.1, the paper states the bound at $W = W(t)$; the proof (Appendix C.2) uses only $W \in S_B$, so it is posed for every random $W$ in $S_B$. In the paper $c_1$ is the constant of Lemmas H.1/5.1 and $c_2$ that of Lemma H.2; here both are existentially quantified before $m$, $B$, $\bar r$, $\gamma$, $\mu$ and $W$.
-- source:
--   Cai, Yang, Lee, Wang, Neural temporal-difference and Q-learning provably converge to global optima, arXiv:1905.10027v2, p. 12, Lemma 5.2 (proof: Appendix C.2, pp. 29–31)

import Mathlib
import Definitions.Def_NeuralTD_Convergence_Setting

namespace NeuralTD.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- Lemma 5.2 (p. 12): local linearization of the population semigradient, posed for every random
`W` in `S_B`; `c₁, c₂` depend only on `c₀` and `d`. -/
theorem lemma_5_2 (d : ℕ) (hd : 3 ≤ d) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (B : ℝ), 0 ≤ B →
      ∀ (rbar γ : ℝ), 0 ≤ rbar → 0 ≤ γ → γ < 1 → ∀ (μ : Measure (Sample d)),
      IsSamplingLaw d rbar μ → Assumption43 c0 μ →
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
        (W : Init m d × Ξ → Param m d), Measurable W → (∀ p, ‖W p - p.1.2‖ ≤ B) →
        ∫⁻ p, ENNReal.ofReal (‖gbar γ μ p.1.1 (W p) - gbarLin γ μ p.1.1 p.1.2 (W p)‖ ^ 2)
          ∂((initLaw m d).prod ν)
          ≤ ENNReal.ofReal ((56 * c1 * B ^ 3 + 24 * c2 * B + 6 * c1 * B * rbar ^ 2) *
              (m : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end NeuralTD.Convergence
