-- Prove2me | Theorems.Thm_HogFarm_SalesAlloc_preservation
-- name    : HogFarm.SalesAlloc.preservation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:58.312683+00:00
-- url     : https://prove2.me/theorems/0d3a9eb8-85fa-40bd-aafe-f5b7fa670e2a
-- title:
--   Proof of Proposition 1, Step 1 — concavity in total holding
-- statement:
--   At any period and information state, let $Z\ge0$ be total holding. The expected continuation value and its value net of feeding cost are both concave:
--
--   $$Z\mapsto\beta\mathbb E_tV_{t+1}(W^1_{t+1},W^2_{t+1}+Z),\qquad Z\mapsto G_t(Z).$$
--
--   This is the total-holding consequence of Step 1. It is reused by the break-even and attainment statements. **Formalization Note** At the last period the continuation value is zero.
-- source:
--   Kouvelis, Liu, Qiu & Turcic, Managing Operations of a Hog Farm Facing Volatile Markets, SSRN preprint 3912801 (March 6, 2023), p. 42 (PDF 42), proof of Proposition 1, Step 1

import Mathlib
import Definitions.Def_HogFarm_SalesAlloc_Model

namespace HogFarm.SalesAlloc

/-- The continuation-value consequence of Step 1 of Proposition 1's proof, p. 42. -/
theorem preservation {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hS : M.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ M.T) (ω : Ω) :
    ConcaveOn ℝ (Set.Ici 0) (cont M t ω) ∧
    ConcaveOn ℝ (Set.Ici 0) (holdGain M t ω) := by sorry

end HogFarm.SalesAlloc
