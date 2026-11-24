-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyActualIntegerSmallJumpMassFiniteV1
-- name    : Kyprianou.Ch02.levyActualIntegerSmallJumpMassFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:46:32.166407+00:00
-- url     : https://prove2.me/theorems/23bb928b-fca5-41c7-a52e-d22c4330fe1b
-- title:
--   Finite expected actual small-jump absolute mass on every integer horizon
-- statement:
--   For the original real Levy process with prescribed triplet and integrable truncated first jump moment, the random extended nonnegative sum of absolute actual source jump sizes at most one over each integer horizon is almost everywhere measurable and has finite Lebesgue integral. The proof must use the genuine original-process jump-count compensator and first-moment Campbell identity, allowing infinite small-jump activity. The explicit ENNReal sum detects unsummable paths correctly and supports the almost-sure-to-every-horizon bridge.
-- source:
--   Kyprianou (2006), Chapter 2: large-jump finite-activity property and small-jump first-moment compensator in Lemma 2.12.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyActualIntegerSmallJumpMassFiniteV1
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
    ∀ n : ℕ,
      AEMeasurable (fun ω => ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
           ENNReal.ofReal (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0)) P ∧
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) < ⊤ := by
  sorry
