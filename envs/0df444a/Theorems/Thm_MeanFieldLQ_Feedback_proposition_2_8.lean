-- Prove2me | Theorems.Thm_MeanFieldLQ_Feedback_proposition_2_8
-- name    : MeanFieldLQ.Feedback.proposition_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:15.470222+00:00
-- url     : https://prove2.me/theorems/5ef65db1-de55-4b63-89a8-bde9a1e48eb0
-- title:
--   Proposition 2.8, pp. 2818–2819 — uniform convexity (2.12) and unique solvability of Problem (MF-LQ)
-- statement:
--   Assume (H1)–(H2) with constant $\delta>0$.
--
--   1. **Uniform convexity (2.12).** For every admissible control $u$ and its state $X$ from the initial value $0$,
--   $$J(0;u)\ \ge\ \delta\,\mathbb E\int_0^T|u(s)|^2\,ds .$$
--   2. **Unique solvability.** For every $x\in\mathbb R^n$, Problem (MF-LQ) has an optimal pair $(X^*,u^*)$, and any two optimal controls for $x$ agree $ds\otimes d\mathbb P$-almost everywhere on $[0,T]\times\Omega$.
--
--   Uniform convexity is what turns the stationarity condition of the optimality system into a sufficient condition (Theorem 3.2), and unique solvability provides the optimal pair that the Riccati feedback of Theorem 4.1 represents.
--
--   **Formalization Note.** The paper writes (2.12) as $\Theta_2\ge\delta I$ for the operator with $J(0;u)=\langle\Theta_2u,u\rangle$. The operators $\Theta_i$ are not formalized; (2.12) is stated directly in terms of $J(0;\cdot)$. The constant is the $\delta$ of (H2), which is what the proof on p. 2819 gives.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), pp. 2818–2819, Proposition 2.8 and (2.12)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Setting

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

/-- Proposition 2.8 (pp. 2818–2819): under (H1)–(H2) with constant `δ`, (2.12) holds in the form
`J(0; u) ≥ δ 𝔼∫₀ᵀ |u(s)|² ds` for every admissible `u` (with its state from `x = 0`), and for every
`x` Problem (MF-LQ) has an optimal pair whose control is unique up to `ds ⊗ dP`-null sets. -/
theorem proposition_2_8 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [μ.IsComplete] {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : Peng1990.SMP.IsStdBrownian μ W)
    (T : ℝ≥0) (hT : 0 < T) (d : Data n m)
    (δ : ℝ) (h1 : H1 T d) (h2 : H2 T δ d) :
    (∀ (u : ℝ≥0 → Ω → Fin m → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ),
        Peng1990.SMP.L2F (filt μ hW) μ T u → IsState μ hW T d 0 u X →
          δ * ∫ ω, (∫ s in Set.Icc (0 : ℝ) T, u s.toNNReal ω ⬝ᵥ u s.toNNReal ω) ∂μ
            ≤ cost μ T d u X) ∧
      ∀ x : Fin n → ℝ,
        (∃ (u : ℝ≥0 → Ω → Fin m → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ),
            IsOptimalPair μ hW T d x u X) ∧
        ∀ (u u' : ℝ≥0 → Ω → Fin m → ℝ) (X X' : ℝ≥0 → Ω → Fin n → ℝ),
          IsOptimalPair μ hW T d x u X → IsOptimalPair μ hW T d x u' X' → AEEqOn μ T u u' := by sorry

end MeanFieldLQ.Feedback
