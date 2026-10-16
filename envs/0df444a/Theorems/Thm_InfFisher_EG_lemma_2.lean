-- Prove2me | Theorems.Thm_InfFisher_EG_lemma_2
-- name    : InfFisher.EG.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:33.604572+00:00
-- url     : https://prove2.me/theorems/b59d16e9-ca64-48a2-9be6-bac8fb4b2d13
-- title:
--   Lemma 2, p. 9 — unique reduced dual minimizer and optimal price
-- statement:
--   For the reduced dual objective $\psi(\beta)$ of equation (2), the infimum over positive multiplier vectors is attained at a unique $\beta^*>0$. The full dual program attains its infimum, every optimal multiplier vector equals $\beta^*$, and any optimal price satisfies
--
--   $$p^*=\max_i\beta_i^*v_i\quad\text{almost everywhere}.$$
--
--   This result provides the dual attainment and multiplier uniqueness in Theorem 1.
--
--   **Formalization Note** Positive multipliers implement the paper's $-\log0=+\infty$ convention.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Lemma 2 and (2), p. 9 (PDF 9)

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_EG_Setting

namespace InfFisher.EG

open MeasureTheory

theorem lemma_2 {d n : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i) :
    let μ := volume.restrict Θ
    (∃! β : Fin n → ℝ,
      (∀ i, 0 < β i) ∧
      ∀ β', (∀ i, 0 < β' i) → dualRed μ v B β ≤ dualRed μ v B β') ∧
    (∃ p β, IsDEGOptimal μ v B p β) ∧
    ∀ p β p' β',
      IsDEGOptimal μ v B p β → IsDEGOptimal μ v B p' β' →
      β' = β ∧ p =ᵐ[μ] maxScaled v β := by sorry

end InfFisher.EG
