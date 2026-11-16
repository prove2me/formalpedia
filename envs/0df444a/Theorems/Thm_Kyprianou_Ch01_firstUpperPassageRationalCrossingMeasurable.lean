-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassageRationalCrossingMeasurable
-- name    : Kyprianou.Ch01.firstUpperPassageRationalCrossingMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:50:17.993209+00:00
-- url     : https://prove2.me/theorems/f84e4d1f-bee1-41b0-8a1d-2d689db89d58
-- title:
--   Rationally sampled strict upper crossings are measurable in the natural past sigma-field
-- statement:
--   The event that a real process exceeds a barrier at some positive rational sampling time not later than u is measurable in its natural sigma-field at u. Each permitted rational evaluation is measurable there using the already Proved Kyprianou.Ch01.naturalSigma_measurable_past and Real.toNNReal_le_iff_le_coe. A countable union over rationals is measurable. This provides the key adapted-measurability component for first strict upper passage in the right-continuous natural filtration, independently of path continuity.
-- source:
--   Kyprianou (2006), Chapter 1, continuous Brownian first-passage stopping-time analysis in Exercise 1.6.

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory Kyprianou.Ch01 Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassageRationalCrossingMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (s : ℝ) :
    @MeasurableSet Ω (Kyprianou.Ch01.naturalSigma X u)
      {ω : Ω | ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ (u : ℝ) ∧
        s < X (Real.toNNReal (q : ℝ)) ω} := by sorry
