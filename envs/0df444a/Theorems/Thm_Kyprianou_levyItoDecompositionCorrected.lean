-- Prove2me | Theorems.Thm_Kyprianou_levyItoDecompositionCorrected
-- name    : Kyprianou.levyItoDecompositionCorrected
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:20:53.41069+00:00
-- url     : https://prove2.me/theorems/dfab66e8-5088-4564-be62-ec693d4033f7
-- title:
--   Theorem 2.1: Lévy–Itô decomposition of a general real Lévy triplet (corrected)
-- statement:
--   For every real drift, nonnegative Brownian scale and admissible Lévy measure, construct on one probability space mutually independent Gaussian-drift, large-compound-Poisson and compensated-small-jump Lévy processes. The small-jump process is a square-integrable martingale with almost surely countably many jumps of strict magnitude below one. The sum is a Lévy process whose characteristic function has the exact Lévy–Khintchine exponent in Kyprianou equation (2.5). The sigma-finiteness class argument on the Lévy measure is mathematically implied by the source Lévy-measure condition and must be discharged/removed before source audit.
--   Corrected source-faithful assumptions and pathwise filtration.
-- source:
--   A. E. Kyprianou (2006), Chapter 2, pp. 33–66

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem levyItoDecompositionCorrected
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure) :
    ∃ (hσ : SigmaFinite levyMeasure),
      letI : SigmaFinite levyMeasure := hσ
      ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
        letI : MeasurableSpace Ω := measΩ
        ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
          letI : IsProbabilityMeasure P := probP
          ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
      (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
      (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      (∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) ∧
      (∀ t ω, Xlarge t ω = largeJumpProcess P levyMeasure N t ω) ∧
      ProbabilityTheory.IsLevyProcess Xgauss P ∧
      ProbabilityTheory.IsLevyProcess Xlarge P ∧
      ProbabilityTheory.IsLevyProcess Xsmall P ∧
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale Xsmall ℱ P ∧
      (∀ t, MemLp (Xsmall t) 2 P) ∧
      (∀ᵐ ω ∂P,
        (∀ t : ℝ≥0,
          ContinuousWithinAt (fun s => Xsmall s ω) (Set.Ici t) t) ∧
        Set.Countable
          {t : ℝ≥0 | ¬ ContinuousAt (fun s => Xsmall s ω) t} ∧
        ∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ,
            Tendsto (fun s => Xsmall s ω) (nhdsWithin t (Set.Iio t)) (nhds l) ∧
            (Xsmall t ω ≠ l → |Xsmall t ω - l| < 1)) ∧
      (∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (Xsmall t)) ξ =
          Complex.exp ((((t : ℝ) : ℂ)) *
            ∫ x in Set.Ioo (-1 : ℝ) 1,
              ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure)) ∧
      IndependentLevyItoComponents P Xgauss Xlarge Xsmall ∧
      ProbabilityTheory.IsLevyProcess
        (fun t ω => Xgauss t ω + Xlarge t ω + Xsmall t ω) P ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun
          (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
          Complex.exp ((((t : ℝ) : ℂ)) *
            Kyprianou.Ch01.levyTripleExponent
              ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ) := by sorry

end Kyprianou
