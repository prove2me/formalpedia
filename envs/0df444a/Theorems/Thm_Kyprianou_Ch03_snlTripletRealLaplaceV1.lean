-- Prove2me | Theorems.Thm_Kyprianou_Ch03_snlTripletRealLaplaceV1
-- name    : Kyprianou.Ch03.snlTripletRealLaplaceV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T17:58:12.764408+00:00
-- url     : https://prove2.me/theorems/e9e0eb9a-6022-4454-8608-71f2948706dd
-- title:
--   Spectrally negative triplet gives real nonnegative-parameter Laplace law
-- statement:
--   Use exponential-moment criterion and the Lévy-Khintchine transform on the negative-support triplet. The compensation convention is Ioo (-1) 1; restriction to negative marks leaves the integral unchanged. The drift is T.drift and the nonnegative Gaussian coefficient is sqrt of its variance.
-- source:
--   Kyprianou (2006), Chapters 2-3; parent 063b9d7c-87f6-432a-91c5-8ca8556a76f0.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open scoped Topology

theorem Kyprianou.Ch03.snlTripletRealLaplaceV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T xi))
    (hNegative : T.levyMeasure (Set.Ici (0 : ℝ)) = 0) :
    ∀ (t : NNReal) (θ : ℝ), 0 ≤ θ →
      Integrable (fun w => Real.exp (θ * X t w)) P ∧
      ∫ w, Real.exp (θ * X t w) ∂P =
        Real.exp ((t : ℝ) * AvramDividend.Classical.laplaceExponent
          T.drift (Real.sqrt (T.gaussianVariance : ℝ)) T.levyMeasure θ) := by
  sorry
