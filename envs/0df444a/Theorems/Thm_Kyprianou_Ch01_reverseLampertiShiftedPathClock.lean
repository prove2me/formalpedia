-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedPathClock
-- name    : Kyprianou.Ch01.reverseLampertiShiftedPathClock
-- status  : Disproved
-- author  : @pageman
-- created : 2026-11-23T16:56:47.551937+00:00
-- url     : https://prove2.me/theorems/bcc2925f-f349-4e8e-bc7d-3dfa0df5a451
-- title:
--   Reverse Lamperti population follows a shifted path
-- statement:
--   Let $y$ be a positive integer and let $A$ be a nonnegative physical time with $A\le yt$. Suppose an integer-valued path $X$ stays at height $y$ on the half-open interval $[0,A)$, and that from time $A$ onward it agrees with a second integer path $Y$ read on the shifted clock $u\mapsto u-A$.
--
--   Write $\theta$ for the inverse of the reciprocal-occupation clock, stopped at the first negative passage. Then the reverse-Lamperti population of $X$ at branching time $t$ equals the reverse-Lamperti population of $Y$ at the residual time $t-A/y$:
--
--   $$
--   Y^{X}_{t}=Y^{Y}_{t-A/y}.
--   $$
--
--   Both sides are read as nonnegative integers, so a path that has already been absorbed at $0$ contributes $0$.
--
--   This is the deterministic clock step in the first-arrival decomposition of the reverse Lamperti process. The compound-Poisson path supplies the constant prefix and the shifted tail; this statement turns those two path facts into the equality of populations.
--
--   **Formalization Note** The population is `compoundPoissonToBranching`, and the residual time is `Real.toNNReal (t - A / y)`. The value is compared after `Int.toNat`.
-- source:
--   Kyprianou (2006), Section 1.3.4, first-jump decomposition of the inverse Lamperti occupation clock.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiShiftedPathClock
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω) :
    (compoundPoissonToBranching X t ω).toNat =
      (compoundPoissonToBranching Y
        (Real.toNNReal ((t : ℝ) - A / (y : ℝ))) ω).toNat := by
  sorry
