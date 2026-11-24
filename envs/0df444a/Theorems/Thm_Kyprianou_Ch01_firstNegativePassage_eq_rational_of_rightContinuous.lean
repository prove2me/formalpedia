-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNegativePassage_eq_rational_of_rightContinuous
-- name    : Kyprianou.Ch01.firstNegativePassage_eq_rational_of_rightContinuous
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T17:56:39.903188+00:00
-- url     : https://prove2.me/theorems/8daf3cdd-79ab-4c78-aa2d-826504cea67b
-- title:
--   Right-continuous first-negative passage equals its rational clock
-- statement:
--   For an integer-valued right-continuous path, the source first strict-negative passage equals the countable positive-rational clock. This is the strict-negative analogue of the proved `firstNonpositiveLatticeEqRationalOfRightContinuous`, and is the correct regularity setting for rational identification.
-- source:
--   Kyprianou (2006), Section 1.3.4; analogue of Prove2Me 63f8b2f6-625b-42e0-9e2a-c94f66721b02 with strict negativity and $t>0$.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNegativePassage_eq_rational_of_rightContinuous
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (hright : ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Set.Ici t) t) :
    firstNegativePassage X ω =
      ⨅ r : ℚ,
        if 0 < (r : ℝ) ∧ X (Real.toNNReal (r : ℝ)) ω < 0 then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤ := by
  sorry
