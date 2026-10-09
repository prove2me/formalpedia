-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_measurable_prefix_vector
-- name    : NestedSeatAlloc.IntPolicy.measurable_prefix_vector
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:10:00.035346+00:00
-- url     : https://prove2.me/theorems/339eca10-250f-4f4a-8c74-95b312177236
-- title:
--   The higher-fare demand prefix is a measurable finite vector
-- statement:
--   # Finite higher-fare demand prefix is a measurable vector
--
--   For the source demand family X satisfying IsSeatModel P X f, every
--   coordinate X i is measurable. The vector of all demand coordinates
--   indexed by Finset.Icc 1 k is measurable as a map into the dependent
--   function type ((i : Finset.Icc 1 k) -> Real). Mathlib's
--   measurable_pi_iff reduces that goal to measurability of each component,
--   directly supplied by hM.meas.
--
--   This is an exact component needed to apply integral_map,
--   integrable_map_measure, and iIndepFun.indepFun_finset in the
--   independence-based proof of expRevenue_eq_integral_condRevenue.
--   The proof does not run local Lean and must be remotely checked.
-- source:
--   # Finite higher-fare demand prefix is a measurable vector
--
--   For the source demand family X satisfying IsSeatModel P X f, every
--   coordinate X i is measurable. The vector of all demand coordinates
--   indexed by Finset.Icc 1 k is measurable as a map into the dependent
--   function type ((i : Finset.Icc 1 k) -> Real). Mathlib's
--   measurable_pi_iff reduces that goal to measurability of each component,
--   directly supplied by hM.meas.
--
--   This is an exact component needed to apply integral_map,
--   integrable_map_measure, and iIndepFun.indepFun_finset in the
--   independence-based proof of expRevenue_eq_integral_condRevenue.
--   The proof does not run local Lean and must be remotely checked.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.measurable_prefix_vector
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) :
    Measurable (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) := by sorry
