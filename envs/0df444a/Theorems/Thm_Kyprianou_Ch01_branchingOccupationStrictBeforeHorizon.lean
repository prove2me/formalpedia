-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOccupationStrictBeforeHorizon
-- name    : Kyprianou.Ch01.branchingOccupationStrictBeforeHorizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:52:52.76228+00:00
-- url     : https://prove2.me/theorems/17e80e14-1f8c-46c1-b8c3-cbab428768f0
-- title:
--   Positive population implies strictly increasing forward occupation clock before extinction
-- statement:
--   For a natural-valued population sample path locally interval integrable from time zero and strictly positive at all times earlier than a finite horizon, the Lamperti occupation clock J(t)=∫0^t Y(s)ds is strictly increasing for any pair a<b before that horizon. Since population values are natural and positive they are at least one, giving J(b)-J(a)>=b-a>0. This is the pathwise strict-clock premise needed by the exact inverse-clock recovery of equation (1.17), with no assumptions after extinction.
-- source:
--   Kyprianou (2006), Chapter 1 equation (1.17), occupation time-change before extinction

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOccupationStrictBeforeHorizon
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (hlocalint : ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume 0 (t : ℝ))
    (horizon : ℝ≥0)
    (hpositive : ∀ t : ℝ≥0, t < horizon → 0 < Y t ω) :
    ∀ a b : ℝ≥0, a < b → b < horizon →
      branchingOccupation Y a ω < branchingOccupation Y b ω := by
  sorry
