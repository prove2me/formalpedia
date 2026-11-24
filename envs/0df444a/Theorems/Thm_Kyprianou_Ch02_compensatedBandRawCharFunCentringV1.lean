-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedBandRawCharFunCentringV1
-- name    : Kyprianou.Ch02.compensatedBandRawCharFunCentringV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:25:38.519796+00:00
-- url     : https://prove2.me/theorems/d004e928-b652-417a-b4e6-386d9fa2f7da
-- title:
--   Compensated finite Poisson band: deterministic shift of the raw characteristic function
-- statement:
--   The compensated band is the raw Poisson integral translated by its deterministic compensator. Use the proved finite-band L2 martingale for almost-everywhere measurability and the Mathlib characteristic-function translation law.
-- source:
--   Kyprianou (2006), Theorem 2.1, compensated finite Poisson bands; exact reduction of sourceFaithfulCompensatedBandCharFunKLSV1.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.compensatedBandRawCharFunCentringV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (Kyprianou.compensatedSmallJumpBand P levyMeasure N e t)) ξ =
      charFun (P.map (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e ≤ |x| ∧ |x| < 1}),
        z.2 ∂(N.N ω))) ξ *
      Complex.exp ((-(((t : ℝ) : ℂ))) *
        ((∫ x in {x : ℝ | e ≤ |x| ∧ |x| < 1}, x ∂levyMeasure : ℝ) : ℂ) *
        (ξ : ℂ) * Complex.I) := by sorry
