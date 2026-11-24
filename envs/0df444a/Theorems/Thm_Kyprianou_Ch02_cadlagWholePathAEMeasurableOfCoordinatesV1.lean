-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagWholePathAEMeasurableOfCoordinatesV1
-- name    : Kyprianou.Ch02.cadlagWholePathAEMeasurableOfCoordinatesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:20:35.402597+00:00
-- url     : https://prove2.me/theorems/d6d70620-1111-44ff-b3e1-e92a0bd810ca
-- title:
--   Regularise almost-everywhere measurable cadlag coordinate paths into a measurable whole-path version
-- statement:
--   Let an arbitrary real process have a.s. cadlag paths and almost everywhere measurable coordinates at every fixed time. Show its entire path-valued map is AEMeasurable into the product sigma-algebra. Use a countable dense dyadic time grid, measurable time-slice representatives and one conull event, then reconstruct all real-time cadlag evaluations from right limits. Do not use aemeasurable_pi_iff naively over the uncountable index NNReal. A completely generic result with no Levy assumptions, connecting to the Chapter 2 physical jump-mass measurability leaf.
-- source:
--   Kyprianou (2006) Chapter 2 source-Levy regularity; LeanLevy imported Processes.StochasticProcess and Processes.LevyProcess

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagWholePathAEMeasurableOfCoordinatesV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (hcad : ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 => X t ω))
    (hcoord : ∀ t : ℝ≥0, AEMeasurable (X t) P) :
    AEMeasurable (fun ω : Ω => fun t : ℝ≥0 => X t ω) P := by
  sorry
