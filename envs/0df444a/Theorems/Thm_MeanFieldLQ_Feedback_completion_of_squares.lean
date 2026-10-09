-- Prove2me | Theorems.Thm_MeanFieldLQ_Feedback_completion_of_squares
-- name    : MeanFieldLQ.Feedback.completion_of_squares
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:39.213574+00:00
-- url     : https://prove2.me/theorems/bf744c24-5da2-4212-8743-72dcacadfe73
-- title:
--   Proof of Theorem 4.1, p. 2828 — J(x; u) − ⟨Π(0)x, x⟩ = 𝔼∫₀ᵀ (|Σ₀^{1/2}w₀|² + |Σ₁^{1/2}w₁|²) ds ≥ 0
-- statement:
--   Assume (H1)–(H2). Let $P$ solve (4.8) with $P(s)\ge0$ on $[0,T]$, and let $\Pi$ solve (4.9). For every $x\in\mathbb R^n$, every admissible control $u$ and its state $X$,
--   $$J(x;u)-\langle\Pi(0)x,x\rangle=\mathbb E\int_0^T\Big(\langle\Sigma_0w_0,w_0\rangle+\langle\Sigma_1w_1,w_1\rangle\Big)ds\ \ge\ 0,$$
--   where
--   $$w_0=u-\mathbb E[u]+\Sigma_0^{-1}(B^TP+D^TPC)(X-\mathbb E[X]),\qquad w_1=\mathbb E[u]+\Sigma_1^{-1}\big((B+\bar B)^T\Pi+(D+\bar D)^TP(C+\bar C)\big)\mathbb E[X].$$
--
--   This identity is the verification step of Theorem 4.1. It gives the lower bound $\langle\Pi(0)x,x\rangle$ for the cost, attained exactly when both squares vanish, that is, along the feedback control.
--
--   **Formalization Note.** The paper writes $|\Sigma_i^{1/2}w_i|^2$, which equals the quadratic form $\langle\Sigma_iw_i,w_i\rangle$ for $\Sigma_i\ge0$; the quadratic form is used.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), p. 2828, proof of Theorem 4.1 (first and last lines of the displayed computation)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Riccati

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

/-- Proof of Theorem 4.1 (p. 2828), completion of squares: under (H1)–(H2), let `P` solve (4.8) with
`P ≥ 0` on `[0, T]` and `Π` solve (4.9). For every `x`, every admissible control `u` and its state
`X`,
`J(x; u) − ⟨Π(0)x, x⟩ = 𝔼∫₀ᵀ (⟨Σ₀w₀, w₀⟩ + ⟨Σ₁w₁, w₁⟩) ds ≥ 0`, where
`w₀ = u − 𝔼[u] + Σ₀⁻¹(BᵀP + DᵀPC)(X − 𝔼[X])` and
`w₁ = 𝔼[u] + Σ₁⁻¹((B + B̄)ᵀΠ + (D + D̄)ᵀP(C + C̄))𝔼[X]`. -/
theorem completion_of_squares {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [μ.IsComplete] {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : Peng1990.SMP.IsStdBrownian μ W)
    (T : ℝ≥0) (hT : 0 < T) (d : Data n m)
    (δ : ℝ) (h1 : H1 T d) (h2 : H2 T δ d) (P Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (hP : IsRiccatiP T d P) (hPpsd : ∀ s ≤ T, (P s).PosSemidef) (hPi : IsRiccatiPi T d P Pi)
    (x : Fin n → ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (hu : Peng1990.SMP.L2F (filt μ hW) μ T u) (hX : IsState μ hW T d x u X) :
    cost μ T d u X - (Pi 0 *ᵥ x) ⬝ᵥ x
        = ∫ ω, (∫ s in Set.Icc (0 : ℝ) T,
            ((Sigma0 d P s.toNNReal *ᵥ gap0 μ d P u X s.toNNReal ω) ⬝ᵥ gap0 μ d P u X s.toNNReal ω
              + (Sigma1 d P s.toNNReal *ᵥ gap1 μ d P Pi u X s.toNNReal)
                  ⬝ᵥ gap1 μ d P Pi u X s.toNNReal)) ∂μ ∧
      0 ≤ ∫ ω, (∫ s in Set.Icc (0 : ℝ) T,
            ((Sigma0 d P s.toNNReal *ᵥ gap0 μ d P u X s.toNNReal ω) ⬝ᵥ gap0 μ d P u X s.toNNReal ω
              + (Sigma1 d P s.toNNReal *ᵥ gap1 μ d P Pi u X s.toNNReal)
                  ⬝ᵥ gap1 μ d P Pi u X s.toNNReal)) ∂μ := by sorry

end MeanFieldLQ.Feedback
