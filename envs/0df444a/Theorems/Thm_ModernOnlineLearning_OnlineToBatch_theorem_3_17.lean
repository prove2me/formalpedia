-- Prove2me | Theorems.Thm_ModernOnlineLearning_OnlineToBatch_theorem_3_17
-- name    : ModernOnlineLearning.OnlineToBatch.theorem_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:02.527651+00:00
-- url     : https://prove2.me/theorems/63f1253a-dca8-4b39-a507-9bb7dbf7b755
-- title:
--   Theorem 3.17 — validation over a finite set
-- statement:
--   Fix a nonempty finite set $S\subseteq V\subseteq\mathbb R^d$ before drawing $T\ge1$ independent samples from $\rho$. Let $f(x,z)\in[0,1]$, define $F(x)=\mathbb E_{z\sim\rho}[f(x,z)]$, and choose a measurable empirical-risk minimizer $\widehat x\in S$ of $T^{-1}\sum_{t=1}^T f(x,\xi_t)$. For $0<\delta<1$, with probability at least $1-\delta$,
--
--   $$F(\widehat x)\le\min_{x\in S}F(x)+2\sqrt{\frac{2\ln(2|S|/\delta)}{T}}.$$
--
--   This validates a predictor selected from finitely many candidates using fresh data.
--
--   **Formalization Note** Nonemptiness makes the empirical minimizer and the real infimum meaningful. Measurability of $f(x,\cdot)$ for $x\in V$ and of the selected minimizer is explicit. The minimum is represented by the infimum over a nonempty finite bounded-risk set.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 3.17, pp. 31–32 (PDF pp. 43–44)

import Mathlib
import Definitions.Def_ModernOnlineLearning_OnlineToBatch_Defs

namespace ModernOnlineLearning.OnlineToBatch

/-- Orabona, arXiv:1912.13213v10, Theorem 3.17, pp. 31–32. -/
theorem theorem_3_17 (d : ℕ) {D : Type*} [MeasurableSpace D]
    (ρ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ρ]
    (V : Set (Decision d)) (S : Finset (Decision d)) (f : Decision d → D → ℝ)
    (T : ℕ) (δ : ℝ) (xHat : (ℕ → D) → Decision d)
    (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : S.Nonempty) (hSV : ∀ x ∈ S, x ∈ V)
    (hf_meas : ∀ x ∈ V, Measurable (f x))
    (hf_bounds : ∀ x ∈ V, ∀ z, 0 ≤ f x z ∧ f x z ≤ 1)
    (hxHat : ∀ ω, xHat ω ∈ S)
    (hxMin : ∀ ω, ∀ x ∈ S, empiricalRisk f ω (xHat ω) T ≤ empiricalRisk f ω x T)
    (hxMeas : Measurable xHat) :
    (MeasureTheory.Measure.infinitePi (fun _ : ℕ => ρ)).real
      {ω : ℕ → D | risk ρ f (xHat ω) ≤ bestRisk ρ f S +
        2 * Real.sqrt (2 * Real.log (2 * (S.card : ℝ) / δ) / (T : ℝ))} ≥
      1 - δ := by sorry

end ModernOnlineLearning.OnlineToBatch
