-- Prove2me | Theorems.Thm_GhadimiLan_TwoPhase_lemma_2_3_a
-- name    : GhadimiLan.TwoPhase.lemma_2_3_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:53.110445+00:00
-- url     : https://prove2.me/theorems/a680cc43-2ce7-4139-9ae5-b87088596dc7
-- title:
--   Lemma 2.3(a) — squared norm of martingale differences
-- statement:
--   Let $\zeta_i\in\mathbb R^n$ be integrable martingale differences adapted to a filtration, and suppose $\mathbb E\|\zeta_i\|^2\le\sigma_i^2$ for every $i\ge1$. Then for each $N\ge1$,
--
--   $$\mathbb E\left\|\sum_{i=1}^N\zeta_i\right\|^2\le\sum_{i=1}^N\sigma_i^2.$$
--
--   If the variance sum is positive, the same statement gives, for $\lambda\ge0$,
--
--   $$\Pr\left\{\left\|\sum_{i=1}^N\zeta_i\right\|^2\ge\lambda\sum_{i=1}^N\sigma_i^2\right\}\le\lambda^{-1},$$
--
--   with the right side interpreted as infinity at $\lambda=0$. This vector-valued estimate controls post-optimization sampling error.
--
--   **Formalization Note** The statement works over a general probability space and does not require a trivial time-zero sigma-algebra, as the paper's application knows each candidate at time zero. The positive-sum guard repairs the printed non-strict tail claim when every $\sigma_i=0$; then its event is certain for every positive $\lambda$.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Lemma 2.3(a), p. 11

import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Lemma 2.3(a), p. 11. The tail clause needs a positive variance sum:
with every `σᵢ = 0`, the printed non-strict event has probability one for all λ. -/
theorem lemma_2_3_a {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (ζ : ℕ → Ω → GhadimiLan.RSG.E n) (σi : ℕ → ℝ)
    (hadapt : ∀ i, 1 ≤ i → StronglyMeasurable[ℱ i] (ζ i))
    (hint : ∀ i, 1 ≤ i → Integrable (ζ i) μ)
    (hzero : ∀ i, 1 ≤ i →
      condExp (ℱ (i - 1)) μ (ζ i) =ᵐ[μ] (fun _ => (0 : GhadimiLan.RSG.E n)))
    (hvarint : ∀ i, 1 ≤ i → Integrable (fun ω => ‖ζ i ω‖ ^ 2) μ)
    (hvar : ∀ i, 1 ≤ i →
      (∫ ω, ‖ζ i ω‖ ^ 2 ∂μ) ≤ σi i ^ 2) :
    ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => ‖∑ i ∈ Finset.Icc 1 N, ζ i ω‖ ^ 2) μ ∧
      (∫ ω, ‖∑ i ∈ Finset.Icc 1 N, ζ i ω‖ ^ 2 ∂μ) ≤
        ∑ i ∈ Finset.Icc 1 N, σi i ^ 2 ∧
      (0 < (∑ i ∈ Finset.Icc 1 N, σi i ^ 2) →
        ∀ lam : ℝ, 0 ≤ lam →
          μ {ω | lam * (∑ i ∈ Finset.Icc 1 N, σi i ^ 2) ≤
            ‖∑ i ∈ Finset.Icc 1 N, ζ i ω‖ ^ 2} ≤
              (ENNReal.ofReal lam)⁻¹) := by sorry

end GhadimiLan.TwoPhase
