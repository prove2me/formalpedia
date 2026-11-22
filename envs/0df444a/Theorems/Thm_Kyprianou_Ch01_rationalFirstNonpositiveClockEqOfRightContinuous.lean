-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rationalFirstNonpositiveClockEqOfRightContinuous
-- name    : Kyprianou.Ch01.rationalFirstNonpositiveClockEqOfRightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:19:13.026247+00:00
-- url     : https://prove2.me/theorems/d98599a5-9b89-45f7-bc1e-63e4b82418aa
-- title:
--   Right-continuous lattice first-nonpositive clock agrees with rational first-hit clock
-- statement:
--   For any right-continuous path f from NNReal into the discrete lattice Int, the extended first-nonpositive clock defined as the infimum of all nonpositive time evaluations in WithTop NNReal is equal to the infimum over rational sample times, using Real.toNNReal. No positive-time restriction is required, so an initial nonpositive state is handled; if no nonpositive time exists both sides are top. Proof is via the order infimum universal property and right-continuous persistence of the lattice inequality f≤0 on a short right neighbourhood, followed by rational density. This supplies the pathwise equality needed to combine the public measurable rational clock with the actual firstNonpositiveLattice of the Lamperti compound Poisson driver.
-- source:
--   Kyprianou 2006 Ch01 §1.3.4. Adapted from the actual accepted private proof lower_clock_rational within Kyprianou.Ch08.StageB.source_result81_measurable_ruin_path_reward (UUID dc6b99ef-9dde-4418-8812-e17bdc341495), with strict negative/open positive-time modified to nonpositive lattice and all times. Supports firstNonpositiveLatticeAEMeasurableFromDriver ea3122ce-4c2e-4917-9682-8ac701d400ca and public rationalFirstNonpositiveLatticeClockMeasurable 334ca786-7cbc-43cf-92d2-95adb1216fab.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rationalFirstNonpositiveClockEqOfRightContinuous
    (f : ℝ≥0 → ℤ)
    (hright : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t) :
    (sInf {y : WithTop ℝ≥0 |
      ∃ u : ℝ≥0, (u : WithTop ℝ≥0) = y ∧ f u ≤ 0}) =
    ⨅ r : ℚ,
      if f (Real.toNNReal (r : ℝ)) ≤ 0 then
        ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
      else ⊤ := by
  sorry
