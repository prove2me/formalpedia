-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyActualSmallJumpAbsoluteSummabilityV1
-- name    : Kyprianou.Ch02.levyActualSmallJumpAbsoluteSummabilityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T21:10:19.721204+00:00
-- url     : https://prove2.me/theorems/5b1393e6-c2a2-456b-b7bd-ce598c9575bb
-- title:
--   Finite absolute sum of genuine original small Levy jumps on every compact horizon
-- statement:
--   For the original real Levy process with prescribed characteristic triplet and an integrable truncated first moment of its Levy jump measure, the actual jump weights with absolute jump size at most one are summable over each compact positive-time interval, simultaneously on one full-measure event. Prove from the jump counting compensator and its Campbell expectation; large jumps are excluded so no large-jump first moment is assumed.
-- source:
--   Kyprianou (2006), Chapter 2: large-jump finite-activity property and small-jump first-moment compensator in Lemma 2.12.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyActualSmallJumpAbsoluteSummabilityV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure →
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
        if |X (s : ℝ≥0) ω - Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ) then |X (s : ℝ≥0) ω - Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| else 0) := by
  sorry
