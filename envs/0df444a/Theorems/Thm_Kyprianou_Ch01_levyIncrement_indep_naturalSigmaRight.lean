-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyIncrement_indep_naturalSigmaRight
-- name    : Kyprianou.Ch01.levyIncrement_indep_naturalSigmaRight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:01:37.49846+00:00
-- url     : https://prove2.me/theorems/905b504d-7107-4c93-97df-7b2e72cf6b4c
-- title:
--   Lévy future increment is independent of the right-natural filtration of the shifted price
-- statement:
--   For the original measurable real-valued Lévy process with continuous paths, a future increment X_t−X_s is independent of the true right-continuous natural sigma algebra at s, including the shifted observable x+X_t. Independence at the ordinary natural sigma algebra is already Proved as Kyprianou.Ch01.levyIncrement_indep_naturalSigma. Prove the extension to the right-natural sigma by approximating s from above, using the all-path continuity, and the Proved AvramDividend.Classical.levy_rightCont_indep_from_sequence method adapted to the original IsLevyProcess structure. The case s=t is deterministic zero. This is a necessary specific probability input for the existing mission-connected Brownian conditional-transition theorem.
-- source:
--   Lévy/Brownian independent increments relative to the right-continuous natural filtration; Kyprianou (2006) Ch 1.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.levyIncrement_indep_naturalSigmaRight
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (x : ℝ)
    (hX : IsLevyProcess X P)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap
        (fun ω : Ω => X t ω - X s ω) inferInstance)
      (naturalSigmaRight (fun u ω => x + X u ω) s) P := by sorry
