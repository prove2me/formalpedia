-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagOfUniformSmallJumpBandFromCadlagBandsV1
-- name    : Kyprianou.Ch02.cadlagOfUniformSmallJumpBandFromCadlagBandsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:52:27.046887+00:00
-- url     : https://prove2.me/theorems/448bc5ff-19bc-4714-ab1c-2c93035355e4
-- title:
--   Almost-sure uniform-on-compact limit of càdlàg small-jump bands is càdlàg
-- statement:
--   Given almost-sure càdlàg finite-cutoff compensated Poisson bands and the original deterministic subsequence convergence uniformly on each finite horizon, prove the limit has a common almost-sure right-continuous and left-limit sample-path event. Use countable integer horizons, countable intersection of regularity events, and the deterministic uniform limit closure of càdlàg functions.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, uniform càdlàg closure

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem cadlagOfUniformSmallJumpBandFromCadlagBandsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
    (hband : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
        (fun (t : ℝ≥0) => compensatedSmallJumpBand P levyMeasure N ε t ω))
    (huniform :
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ)) :
      (∀ᵐ ω ∂P,
        (∀ t : ℝ≥0,
          ContinuousWithinAt (fun s => M s ω) (Set.Ici t) t) ∧
        ∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ,
            Tendsto (fun s => M s ω)
              (nhdsWithin t (Set.Iio t)) (nhds l))
    := by sorry
end Kyprianou.Ch02
