-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiConstantPrefixPhysicalRestart
-- name    : Kyprianou.Ch01.reverseLampertiConstantPrefixPhysicalRestart
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:17:11.660217+00:00
-- url     : https://prove2.me/theorems/50423a33-0479-4957-8932-5757996f07d5
-- title:
--   Reverse-Lamperti time change commutes with a constant-prefix physical-path restart
-- statement:
--   Suppose a nonexplosive integer physical path equals a positive constant y up to physical time a, and its entire continuation is a shifted path Y. At branching time t beyond the initial holding time a/y, its inverse-Lamperti transformed and extinction-stopped population equals the inverse-Lamperti transform of the continuation at residual branching time t-a/y. Handle infinite inverse clocks and extinction at the first jump.
-- source:
--   Deterministic reciprocal-occupation clock additivity and right-inverse time-change identity for Kyprianou (2006) section 1.3.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiConstantPrefixPhysicalRestart
    {Ω : Type*}
    (X Y : ℝ≥0 → Ω → ℤ) (w : Ω)
    (y : ℕ) (hy : 0 < y)
    (a : ℝ) (ha : 0 < a)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a → X u w = (y : ℤ))
    (hSuffix : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      X u w = Y (Real.toNNReal ((u : ℝ) - a)) w)
    (hNoExplosionX : ∀ t : ℝ≥0, ∃ s : ℝ≥0,
      (t : ℝ≥0∞) < reciprocalOccupation X s w)
    (t : ℝ≥0) (ht : a ≤ (y : ℝ) * (t : ℝ)) :
    (compoundPoissonToBranching X t w).toNat =
      (compoundPoissonToBranching
        Y (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) w).toNat := by
  sorry
