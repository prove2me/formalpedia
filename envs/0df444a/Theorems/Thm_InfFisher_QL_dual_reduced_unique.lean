-- Prove2me | Theorems.Thm_InfFisher_QL_dual_reduced_unique
-- name    : InfFisher.QL.dual_reduced_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:12.021044+00:00
-- url     : https://prove2.me/theorems/421804af-da7e-4b62-a737-8d0afc668501
-- title:
--   Proof of Theorem 10(b), p. a21 — reduced dual has a unique minimizer
-- statement:
--   Let $m_\beta(\theta)=\max_i\beta_i v_i(\theta)$ and define the reduced dual objective
--   $$D(\beta)=\int_\Theta m_\beta(\theta)\,d\mu(\theta)-\sum_i B_i\log\beta_i.$$
--   Under the standing market assumptions, $D$ has exactly one minimizer among vectors satisfying $0<\beta_i\le1$ for every buyer.
--
--   The reduction identifies the utility-price vector used in the optimal dual pair of Theorem 10(b).
--
--   **Formalization Note** Positivity of $\beta_i$ represents the dual objective's infinite value at zero. The pointwise maximum is an indexed supremum over the finite buyer type.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, proof of Theorem 10(b), p. a21

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_QL_Setting

namespace InfFisher.QL

open MeasureTheory

theorem dual_reduced_unique
    {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i)
  :
    let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict Θ
    ∃! β : Fin n → ℝ,
      (∀ i, 0 < β i ∧ β i ≤ 1) ∧
      ∀ β', (∀ i, 0 < β' i ∧ β' i ≤ 1) →
        InfFisher.EG.dualRed μ v B β ≤ InfFisher.EG.dualRed μ v B β'  := by sorry
end InfFisher.QL
