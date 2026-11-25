-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableCompensationFiniteBandFromRectangleCounts
-- name    : Kyprianou.Ch04.predictableCompensationFiniteBandFromRectangleCounts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:54:32.419705+00:00
-- url     : https://prove2.me/theorems/3681511e-ff60-419a-94b9-6b0eb08c767a
-- title:
--   Finite-band predictable compensation from rectangle identities
-- statement:
--   Construct the expected raw and deterministic intensity clock measures on the finite mark band. Their masses agree on the initial atom and future predictable rectangles, so the proved finite marked predictable measure uniqueness theorem applies.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Finite-band extension using expected marked clock measures. -/
theorem predictableCompensationFiniteBandFromRectangleCounts
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hRect : ∀ (u v : NNReal) (B : Set Real) (A : Set Omega),
      u ≤ v → MeasurableSet B → MeasurableSet[F u] A →
      (∫⁻ omega, N.N omega (Set.Ioc (u : Real) (v : Real) ×ˢ B) *
        A.indicator (fun _ => (1 : ENNReal)) omega ∂P) =
      referenceIntensity levyMeasure (Set.Ioc (u : Real) (v : Real) ×ˢ B) * P A)
    (t : NNReal) (B : Set Real) (hB : MeasurableSet B)
    (hBfin : levyMeasure B < ⊤)
    (f : ((NNReal × Omega) × Real) → ENNReal) (hf : Measurable[F.predictable.prod inferInstance] f) :
    (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
        f ((z.1.toNNReal, w), z.2) ∂(N.N w) ∂P) =
    (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
        f ((z.1.toNNReal, w), z.2) ∂(referenceIntensity levyMeasure) ∂P) := by
  sorry
end Kyprianou.Ch04
