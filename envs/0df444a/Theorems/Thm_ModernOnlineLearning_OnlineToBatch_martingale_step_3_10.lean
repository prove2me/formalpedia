-- Prove2me | Theorems.Thm_ModernOnlineLearning_OnlineToBatch_martingale_step_3_10
-- name    : ModernOnlineLearning.OnlineToBatch.martingale_step_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:13.146736+00:00
-- url     : https://prove2.me/theorems/bd9c9ac6-df21-47c8-8423-de6d03cd76de
-- title:
--   Proof of Theorem 3.10 — the adaptive-prediction concentration step
-- statement:
--   Draw $T\ge1$ samples independently from $\rho$. Let $f(x,z)\in[0,1]$ be measurable in $z$ for every $x\in V$, and let the deterministic online rule $A$ predict $x_t\in V$ using only samples before round $t$. Put $F(x)=\mathbb E_{z\sim\rho}[f(x,z)]$. For $0<\delta<1$, with probability at least $1-\delta/2$,
--
--   $$\frac1T\sum_{t=1}^T F(x_t)\le\frac1T\sum_{t=1}^T f(x_t,\xi_t)+\sqrt{\frac{2\ln(2/\delta)}{T}}.$$
--
--   This is the first concentration bound in the proof of Theorem 3.10, for the sample-dependent predictions.
--
--   **Formalization Note** The sample space is the infinite product of $\rho$, and probabilities are real-valued. Measurability of each prediction, realized loss, and realized true risk is stated explicitly so the event and integrals are genuine.
-- source:
--   Orabona, arXiv:1912.13213v10, §3.1.2, proof of Theorem 3.10, p. 28 (PDF p. 40), display after “Thus, with probability at least 1 − δ/2”

import Mathlib
import Definitions.Def_ModernOnlineLearning_OnlineToBatch_Defs

namespace ModernOnlineLearning.OnlineToBatch

/-- Orabona, arXiv:1912.13213v10, §3.1.2, first concentration display in the proof
of Theorem 3.10, p. 28. -/
theorem martingale_step_3_10 (d : ℕ) {D : Type*} [MeasurableSpace D]
    (ρ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ρ]
    (V : Set (Decision d)) (f : Decision d → D → ℝ) (A : ℕ → (ℕ → D) → Decision d)
    (T : ℕ) (δ : ℝ)
    (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hf_meas : ∀ x ∈ V, Measurable (f x))
    (hf_bounds : ∀ x ∈ V, ∀ z, 0 ≤ f x z ∧ f x z ≤ 1)
    (hA : IsOnlineAlgorithm V A)
    (hA_meas : ∀ t ∈ Finset.Icc 1 T, Measurable (A t))
    (hloss_meas : ∀ t ∈ Finset.Icc 1 T,
      Measurable (fun ω : ℕ → D => f (A t ω) (ω t)))
    (hrisk_meas : ∀ t ∈ Finset.Icc 1 T,
      Measurable (fun ω : ℕ → D => risk ρ f (A t ω))) :
    (MeasureTheory.Measure.infinitePi (fun _ : ℕ => ρ)).real
      {ω : ℕ → D |
        (∑ t ∈ Finset.Icc 1 T, risk ρ f (A t ω)) / (T : ℝ) ≤
          (∑ t ∈ Finset.Icc 1 T, f (A t ω) (ω t)) / (T : ℝ) +
            Real.sqrt (2 * Real.log (2 / δ) / (T : ℝ))} ≥ 1 - δ / 2 := by sorry

end ModernOnlineLearning.OnlineToBatch
