-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNegativePassageEqShiftedFirstNonpositive
-- name    : Kyprianou.Ch01.firstNegativePassageEqShiftedFirstNonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:04:41.112344+00:00
-- url     : https://prove2.me/theorems/85ccb3e8-54ec-4ae7-ad8c-68d55eb140ef
-- title:
--   Strict-negative passage equals shifted nonpositive passage for nonnegative initial lattice states
-- statement:
--   For an integer-valued NNReal-indexed path X starting at X(0)≥0, prove its source firstNegativePassage clock, defined as the infimum of strictly positive times with X_t<0 (top if never hit), equals the already available firstNonpositiveLattice clock applied to the pointwise shifted path X+1, defined as infimum of times with X_t+1≤0. Since integer `X_t+1≤0 ↔ X_t<0` and nonnegative X0 means the hitting set excludes t=0, the two hitting sets, existence tests, infima, and top cases agree identically. This is the exact source bridge to reuse the already Proved rationalFirstNonpositiveLatticeClockMeasurable and firstNonpositiveLatticeEqRationalOfRightContinuous; do not assume continuous rather than càdlàg paths or finite first offspring moments.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4, reverse Lamperti Def_Kyprianou_Ch01_LampertiInverse firstNegativePassage; forward Def_Kyprianou_Ch01_ForwardLampertiPaths firstNonpositiveLattice. Parent root ac1b29c6-5525-4344-a03d-7469824736ed, current rootward child reverseLampertiNonexplosiveJointClockVersion 4c40c848-86b4-4c33-8f82-4106ca9fe438. Proved rational clock 334ca786-7cbc-43cf-92d2-95adb1216fab and equality 63f8b2f6-625b-42e0-9e2a-c94f66721b02.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNegativePassageEqShiftedFirstNonpositive
    {Ω : Type*}
    (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (hStart : 0 ≤ X 0 ω) :
    firstNegativePassage X ω =
      firstNonpositiveLattice
        (fun t η => X t η + 1) ω := by
  sorry
