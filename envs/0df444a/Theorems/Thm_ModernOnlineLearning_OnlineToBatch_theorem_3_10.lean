-- Prove2me | Theorems.Thm_ModernOnlineLearning_OnlineToBatch_theorem_3_10
-- name    : ModernOnlineLearning.OnlineToBatch.theorem_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:32.315097+00:00
-- url     : https://prove2.me/theorems/4161e4e6-e488-4d1e-b136-a190e0180186
-- title:
--   Theorem 3.10 — high-probability online-to-batch conversion
-- statement:
--   Let $V\subseteq\mathbb R^d$ and let $F(x)=\mathbb E_{z\sim\rho}[f(x,z)]$ for a loss $f:V\times D\to[0,1]$ measurable in the data argument. Draw $T\ge1$ independent samples from $\rho$. A deterministic, non-anticipating online algorithm predicts $x_t\in V$ and has the pathwise regret guarantee $\operatorname{Regret}_T(u)\le R(u,T)$ for every $u\in V$ and every sample path. Suppose $0<\delta<1$ and $F(u)+R(u,T)/T$ attains its minimum in $V$. Then, with probability at least $1-\delta$,
--
--   $$\frac1T\sum_{t=1}^T F(x_t)\le\min_{u\in V}\left(F(u)+\frac{R(u,T)}{T}\right)+2\sqrt{\frac{2\ln(2/\delta)}{T}}.$$
--
--   A pathwise online regret bound therefore controls true risk under independent sampling, with the deviation constant stated in the book.
--
--   **Formalization Note** The minimum is represented by an explicit minimizer $u_\star$. Predictions use only earlier samples. The sample space is the infinite product of $\rho$. The measurable realized losses and risks are explicit standing requirements needed to interpret the probability statement; $T\ge1$ guards division by $T$. The loss is real-valued on $V$ as in $[0,1]$.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 3.10, p. 27 (PDF p. 39)

import Mathlib
import Definitions.Def_ModernOnlineLearning_OnlineToBatch_Defs

namespace ModernOnlineLearning.OnlineToBatch

/-- Orabona, arXiv:1912.13213v10, Theorem 3.10, p. 27. -/
theorem theorem_3_10 (d : ℕ) {D : Type*} [MeasurableSpace D]
    (ρ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ρ]
    (V : Set (Decision d)) (f : Decision d → D → ℝ) (A : ℕ → (ℕ → D) → Decision d)
    (R : Decision d → ℕ → ℝ) (T : ℕ) (δ : ℝ) (uStar : Decision d)
    (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hf_meas : ∀ x ∈ V, Measurable (f x))
    (hf_bounds : ∀ x ∈ V, ∀ z, 0 ≤ f x z ∧ f x z ≤ 1)
    (hA : IsOnlineAlgorithm V A)
    (hA_meas : ∀ t ∈ Finset.Icc 1 T, Measurable (A t))
    (hloss_meas : ∀ t ∈ Finset.Icc 1 T,
      Measurable (fun ω : ℕ → D => f (A t ω) (ω t)))
    (hrisk_meas : ∀ t ∈ Finset.Icc 1 T,
      Measurable (fun ω : ℕ → D => risk ρ f (A t ω)))
    (hregret : ∀ ω : ℕ → D, ∀ u ∈ V, regret f A ω u T ≤ R u T)
    (huStar : uStar ∈ V)
    (hmin : ∀ u ∈ V,
      risk ρ f uStar + R uStar T / (T : ℝ) ≤
        risk ρ f u + R u T / (T : ℝ)) :
    (MeasureTheory.Measure.infinitePi (fun _ : ℕ => ρ)).real
      {ω : ℕ → D |
        (∑ t ∈ Finset.Icc 1 T, risk ρ f (A t ω)) / (T : ℝ) ≤
          risk ρ f uStar + R uStar T / (T : ℝ) +
            2 * Real.sqrt (2 * Real.log (2 / δ) / (T : ℝ))} ≥ 1 - δ := by sorry

end ModernOnlineLearning.OnlineToBatch
