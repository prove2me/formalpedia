-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyPhysicalSmallJumpMassCampbellIntensityV1
-- name    : Kyprianou.Ch02.levyPhysicalSmallJumpMassCampbellIntensityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:11:47.718802+00:00
-- url     : https://prove2.me/theorems/f0b9a1d9-4796-4de0-9b21-0efaff20f3dc
-- title:
--   Campbell bound for expected actual small-jump mass of original Levy process
-- statement:
--   For the source Levy process with prescribed characteristic exponent/triplet, prove that the extended expected total absolute mass of its actual chronological jumps no larger than one over every integer horizon is bounded by time multiplied by the extended integral of min(1,abs(x)) against the specified Levy measure. The proof requires identifying the physical original jump measure from hX and hchar. Cannot substitute a separately realized Poisson random measure or assume a priori summability.
-- source:
--   Kyprianou (2006), Chapter 2: large-jump finite-activity property and small-jump first-moment compensator in Lemma 2.12.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyPhysicalSmallJumpMassCampbellIntensityV1
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
    ∀ n : ℕ,
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) ≤
          (n : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂levyMeasure) := by
  sorry
