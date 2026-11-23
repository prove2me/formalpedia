-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagOfSmallJumpUniformApproxV1
-- name    : Kyprianou.Ch02.cadlagOfSmallJumpUniformApproxV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:13:03.619454+00:00
-- url     : https://prove2.me/theorems/f449a63b-4d22-46fc-a35c-ca82f207600e
-- title:
--   Theorem 2.10: càdlàg paths from finite-band uniform convergence
-- statement:
--   Almost-sure uniform finite-horizon convergence of compensated Poisson small-jump bands implies right continuity and finite left limits on one common full-measure event. Prove finite-band cadlag first, then countably intersect horizon and convergence events.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, deterministic uniform-limit argument

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
theorem cadlagOfSmallJumpUniformApproxV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
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
