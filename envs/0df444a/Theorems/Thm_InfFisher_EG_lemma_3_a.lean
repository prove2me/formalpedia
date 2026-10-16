-- Prove2me | Theorems.Thm_InfFisher_EG_lemma_3_a
-- name    : InfFisher.EG.lemma_3_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:24.943978+00:00
-- url     : https://prove2.me/theorems/89be4c41-3ed9-4334-8b82-e29f218c9f72
-- title:
--   Lemma 3(a), p. 9 — weak duality
-- statement:
--   Set $C=\sum_i B_i-\sum_i B_i\log B_i$. Every feasible primal allocation with positive buyer utilities and every feasible dual pair with positive multipliers satisfy
--
--   $$C+\sum_iB_i\log\langle v_i,x_i\rangle
--      \le \int p\,d\mu-\sum_iB_i\log\beta_i.$$
--
--   This pointwise inequality yields the paper's $C+z^*\le w^*$ after taking the program optima.
--
--   **Formalization Note** The finite objective inequality states weak duality without using a real supremum or infimum at an empty or unbounded set. Zero utilities and zero multipliers carry the paper's infinite objective values.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Lemma 3(a), p. 9; (A.2), p. a4 (PDF 39)

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_EG_Setting

namespace InfFisher.EG

open MeasureTheory

theorem lemma_3_a {d n : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i) :
    let μ := volume.restrict Θ
    let C := (∑ i, B i) - ∑ i, B i * Real.log (B i)
    ∀ x, IsAllocation μ x →
      (∀ i, 0 < pair μ (v i) (x i)) →
      ∀ p β, IsDEGFeasible μ v p β →
        (∀ i, 0 < β i) →
        C + pegObj μ v B x ≤ degObj μ B p β := by sorry

end InfFisher.EG
