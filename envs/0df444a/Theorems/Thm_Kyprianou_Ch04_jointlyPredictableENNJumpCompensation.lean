-- Prove2me | Theorems.Thm_Kyprianou_Ch04_jointlyPredictableENNJumpCompensation
-- name    : Kyprianou.Ch04.jointlyPredictableENNJumpCompensation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:04:24.012641+00:00
-- url     : https://prove2.me/theorems/7e831188-b055-437b-b5f7-397622267523
-- title:
--   Nonnegative marked Poisson compensation on the predictable product sigma-algebra
-- statement:
--   Identify the expected raw random measure and the deterministic intensity-times-probability measure on predictable rectangles. Extend by sigma-finite measure uniqueness, then integrate the nonnegative predictable function.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Compensation for a jointly predictable nonnegative extended-real marked integrand. -/
theorem jointlyPredictableENNJumpCompensation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (psi : Real → Real → Omega → ENNReal)
    (hPsi : Measurable[F.predictable.prod inferInstance]
      (fun z : (NNReal × Omega) × Real => psi (z.1.1 : Real) z.2 z.1.2)) :
    ∀ t : NNReal,
      (∫⁻ omega, (∫⁻ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
        psi z.1 z.2 omega ∂(N.N omega)) ∂P) =
      (∫⁻ omega, (∫⁻ s in Set.Icc (0 : Real) (t : Real),
        (∫⁻ x, psi s x omega ∂levyMeasure) ∂volume) ∂P) := by
  sorry
end Kyprianou.Ch04
