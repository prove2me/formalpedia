-- Prove2me | Theorems.Thm_InfFisher_EG_lemma_1
-- name    : InfFisher.EG.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:22.486687+00:00
-- url     : https://prove2.me/theorems/247e144b-8d06-4aed-9bc9-89d55ff7bd72
-- title:
--   Lemma 1, pp. 8–9 — feasible utilities are pure, convex, and compact
-- statement:
--   Let $U$ be the utility vectors attainable by feasible allocations and $U'$ those attainable by pure allocations in the continuum Fisher market. Then
--
--   $$U=U',\qquad U\text{ is convex and compact}.$$
--
--   This replaces compactness of the allocation space by compactness of its finite dimensional utility image.
--
--   **Formalization Note** The valuation positivity and budget assumptions of the full market are unnecessary for this utility range assertion.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Lemma 1 and (1), pp. 8–9 (PDF 8–9)

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_EG_Setting

namespace InfFisher.EG

open MeasureTheory

theorem lemma_1 {d n : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i) :
    let μ := volume.restrict Θ
    feasUtil μ v = pureUtil μ Θ v ∧
      Convex ℝ (feasUtil μ v) ∧ IsCompact (feasUtil μ v) := by sorry

end InfFisher.EG
