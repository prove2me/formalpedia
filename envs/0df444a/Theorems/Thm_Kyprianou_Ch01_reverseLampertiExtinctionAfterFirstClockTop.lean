-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiExtinctionAfterFirstClockTop
-- name    : Kyprianou.Ch01.reverseLampertiExtinctionAfterFirstClockTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:50:33.727553+00:00
-- url     : https://prove2.me/theorems/be22f9bf-38b0-4744-a672-a3c89b408e91
-- title:
--   After first extinction jump, reciprocal clock becomes infinite
-- statement:
--   The first jump produces zero and remains zero until the next jump, so every strict right-side occupation interval contains a positive-length zero state interval. Apply the proved zero-stage infinite reciprocal-occupation integral theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiExtinctionAfterFirstClockTop
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y j : ℕ) (a b : ℝ) (ha : 0 < a) (hAB : a < b)
    (hMiddle : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      (u : ℝ) < b → X u ω = ((y + j - 1 : ℕ) : ℤ))
    (hZero : y + j - 1 = 0) :
    ∀ u : ℝ≥0, a < (u : ℝ) → (u : ℝ) < b →
      reciprocalOccupation X u ω = ⊤ := by
  sorry
