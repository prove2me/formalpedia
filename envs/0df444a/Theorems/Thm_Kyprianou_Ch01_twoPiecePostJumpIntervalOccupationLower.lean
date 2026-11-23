-- Prove2me | Theorems.Thm_Kyprianou_Ch01_twoPiecePostJumpIntervalOccupationLower
-- name    : Kyprianou.Ch01.twoPiecePostJumpIntervalOccupationLower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:50:49.216979+00:00
-- url     : https://prove2.me/theorems/e024ab8c-c706-494c-b3e2-9b88e9bff6f3
-- title:
--   Post-first jump source interval provides a lower bound for the inverse-speed occupation integral
-- statement:
--   The reciprocal occupation over (0,c] is at least its restriction to (a,c] because the integrand is nonnegative. Here c=a+(y+j)*t<b and X=z=y+j-1>0 throughout (a,c], so the restricted integral is (c-a)/z=(y+j)*t/z. Formalise with lintegral_mono_set and lintegral_congr_ae.
-- source:
--   Kyprianou (2006) §1.3.4 inverse Lamperti post-mark occupation

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.twoPiecePostJumpIntervalOccupationLower
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y j : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (a b : ℝ) (ha : 0 < a)
    (hAB : a < b)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a →
      X u ω = (y : ℤ))
    (hMiddle : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      (u : ℝ) < b → X u ω = ((y + j - 1 : ℕ) : ℤ))
    (hPost : 0 < y + j - 1)
    (hFirst : a ≤ (y : ℝ) * (t : ℝ))
    (hSecond : a + ((y + j : ℕ) : ℝ) * (t : ℝ) < b) :
    (1 / ((y + j - 1 : ℕ) : ℝ≥0∞)) *
      (((y + j : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)) ≤
      reciprocalOccupation X
        (Real.toNNReal (a + ((y + j : ℕ) : ℝ) * (t : ℝ))) ω := by
  sorry
