-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassageNaturalStoppingContinuous
-- name    : Kyprianou.Ch01.firstUpperPassageNaturalStoppingContinuous
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T21:41:48.436415+00:00
-- url     : https://prove2.me/theorems/bf087980-d521-4740-8778-f532d6fb96bd
-- title:
--   First strict upper passage of a continuous real path is a stopping time for the right-continuous natural filtration
-- statement:
--   A continuous real process whose deterministic evaluations are measurable has its first strict upper-passage time through a positive barrier measurable in the right-continuous natural filtration: the event {T≤t} can be expressed as a countable decreasing intersection of pre-t+epsilon observation crossing events. This right-limit formulation also handles T=0 and no crossing (T=∞) faithfully. It is a deterministic/adapted path lemma required for the inverse Gaussian Brownian first-passage transform and for stopping-time optional sampling. No distributional Brownian or finite-hitting assumption is introduced.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and Exercise 1.6 first-passage stopping time, continuous-path argument.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassageNaturalStoppingContinuous
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (hs : 0 < s) :
    Kyprianou.Ch01.IsNaturalStoppingTime X
      (Kyprianou.Ch01.firstUpperPassage X s) := by sorry
