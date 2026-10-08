-- Prove2me | Theorems.Thm_MFGLimit_Conc_theorem_4_3
-- name    : MFGLimit.Conc.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:52.847712+00:00
-- url     : https://prove2.me/theorems/2c7afe1b-e274-49fe-9ed9-591184689b44
-- title:
--   Theorem 4.3, p. 16 — exponentially close Nash and comparison particle systems
-- statement:
--   Let $X$ solve the Nash state system (2.7) and $\bar X$ solve the comparison system (4.1), with the same initial states and noises. Under Assumption A and either B or B′, constants $\kappa_1,\kappa_2>0$ exist such that for every $\varepsilon>0$ and positive $n\ge\kappa_1/\varepsilon$,
--   $$P\!\left(W_{2,C^d}(m_X^n,m_{\bar X}^n)>\varepsilon\right)\le P\!\left(\frac1n\sum_{i=1}^n\|X^i-\bar X^i\|_\infty^2>\varepsilon^2\right)\le 2n\exp\!\left(-\frac{\varepsilon^2n^2}{\kappa_2}\right).$$
--   The first inequality uses the synchronous matching of each pair of trajectories; the second is the paper's exponential estimate.
--
--   **Formalization Note** $W_2$ acts on the full path-space empirical measures, and all constants precede $n$ and $\varepsilon$. The classical master solution used to define $\bar X$ is the same one appearing in B′ when that alternative applies.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 16, Theorem 4.3, (4.10)

import Mathlib
import Definitions.Def_MFGLimit_Conc_Transport

namespace MFGLimit.Conc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 4.3, including both inequalities of (4.10). -/
theorem theorem_4_3 {Ω A : Type*} [mΩ : MeasurableSpace Ω]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] {d d₀ : ℕ}
    (M : Model Ω A d d₀)
    (v : ∀ n, Fin n → ℝ≥0 → (Fin n → E d) → ℝ)
    (U : ℝ≥0 → E d → Measure (E d) → ℝ)
    (hA : AssumptionA M v) (hU : IsMasterSolution M U)
    (hB : AssumptionB M ∨ AssumptionB' M v U)
    (X Xbar : ∀ n : ℕ, Fin n → Ω → Path d M.T)
    (hX : ∀ n, 1 ≤ n → IsNashState M v (X n))
    (hXbar : ∀ n, 1 ≤ n → IsMVParticle M U (Xbar n)) :
    ∃ κ₁ κ₂ : ℝ, 0 < κ₁ ∧ 0 < κ₂ ∧
      ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ), 1 ≤ n →
      (n : ℝ) ≥ κ₁ / ε →
        M.P {ω | Wp 2
          (empMeas n (fun i => X n i ω))
          (empMeas n (fun i => Xbar n i ω)) > ε} ≤
        M.P {ω | (1 / (n : ℝ)) *
          (∑ i : Fin n, ‖X n i ω - Xbar n i ω‖ ^ 2) > ε ^ 2} ∧
        M.P {ω | (1 / (n : ℝ)) *
          (∑ i : Fin n, ‖X n i ω - Xbar n i ω‖ ^ 2) > ε ^ 2} ≤
          ENNReal.ofReal (2 * (n : ℝ) *
            Real.exp (-(ε ^ 2 * (n : ℝ) ^ 2 / κ₂))) := by sorry

end MFGLimit.Conc
