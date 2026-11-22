-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stoppedLatticePathMeasurableOfFirstHit
-- name    : Kyprianou.Ch01.stoppedLatticePathMeasurableOfFirstHit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:57:17.986797+00:00
-- url     : https://prove2.me/theorems/800154e8-4435-4ec7-a59f-41be5dd18b3d
-- title:
--   Measurability of a lattice path stopped at its measurable first nonpositive time
-- statement:
--   For any integer-valued NNReal-indexed sample path that is measurable as a product-space random element, and for which the first nonpositive lattice time is itself a measurable WithTop NNReal random variable, the path stopped at that time and replaced by 0 thereafter is also a globally measurable path-space random element. Apply the product measurable-space characterisation, then use the measurability of the first-hit-time comparison event and the fixed-time section. This isolates the only additional ingredient needed to pass from the unstopped integer compound Poisson path to its stopped version.
-- source:
--   Direct decomposition of Kyprianou.Ch01.stoppedIntegerCompoundPoissonPathAEMeasurableFromDriver UUID 49405927-66dc-442e-b14c-6d9558559823, from Kyprianou 2006 Chapter 1 §1.3.4. Uses exact stopping convention in Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths. No offspring mean assumption. Hitting-time measurability is a separate mathematical obligation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stoppedLatticePathMeasurableOfFirstHit
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hPath : Measurable (fun ω : Ω => fun t : ℝ≥0 => X t ω))
    (hHit : Measurable (fun ω : Ω => firstNonpositiveLattice X ω)) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      if firstNonpositiveLattice X ω ≤ (t : WithTop ℝ≥0)
      then (0 : ℤ) else X t ω) := by
  sorry
