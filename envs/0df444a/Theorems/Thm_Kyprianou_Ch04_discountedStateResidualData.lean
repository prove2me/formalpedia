-- Prove2me | Theorems.Thm_Kyprianou_Ch04_discountedStateResidualData
-- name    : Kyprianou.Ch04.discountedStateResidualData
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:53:08.401926+00:00
-- url     : https://prove2.me/theorems/4669c846-847b-57a2-88d8-4fc94e733354
-- title:
--   discountedStateResidualData
-- statement:
--   Discounted continuous spatial residuals have bounded right-continuous stopped densities.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory Filter Set Topology ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- Discounted continuous spatial residuals have bounded right-continuous stopped densities. -/
theorem Kyprianou.Ch04.discountedStateResidualData {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (H : ℝ → ℝ) (hH : Continuous H)
    (l : ℝ) (hl : 0 ≤ l)
    (hX : ∀ᵐ w ∂P, IsCadlag (fun t => X t w))
    (hm : ∀ᵐ w ∂P, Measurable (fun r : ℝ => X r.toNNReal w)) :
    let g := fun (r : ℝ) w => Real.exp (-l*r)*H (X r.toNNReal w)
    let tau : ℕ → Ω → WithTop NNReal := fun n w => sInf {v : WithTop NNReal |
      ∃ u : NNReal, v = ↑u ∧ (n:ℝ) < |X u w|}
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ᵐ w ∂P, Measurable (fun r => g r w) ∧
        (∀ s : ℝ, 0 ≤ s → ContinuousWithinAt (fun r => g r w) (Ici s) s) ∧
        (∀ t : NNReal, ∃ n, (t : WithTop NNReal) < tau n w) ∧
        ∀ n : ℕ, ∀ᵐ r ∂volume.restrict (Ici (0 : ℝ)),
          ‖if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0‖ ≤ C n := by
  sorry
