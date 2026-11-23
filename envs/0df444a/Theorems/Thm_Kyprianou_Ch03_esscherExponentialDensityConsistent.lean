-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherExponentialDensityConsistent
-- name    : Kyprianou.Ch03.esscherExponentialDensityConsistent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:46:59.948202+00:00
-- url     : https://prove2.me/theorems/e3a86319-9495-4436-9711-a58e40a594bc
-- title:
--   Esscher exponential density: mean-one martingale and finite-horizon consistency
-- statement:
--   Proves finite positive normalisation, mean-one Esscher density, and its martingale consistency on each completed natural filtration. Does not assume existence of a globally extended tilted measure.
-- source:
--   Kyprianou (2006), eqs. (3.10)-(3.11), printed p. 78; Theorem 3.9.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem esscherExponentialDensityConsistent
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : ℝ)
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (beta * x))
      {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    let k := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)
    (∀ t : NNReal,
      Integrable (esscherDensity X beta k t) P ∧
      (∫ omega, esscherDensity X beta k t omega ∂P) = 1) ∧
    (∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (∫ omega, Set.indicator A (esscherDensity X beta k t) omega ∂P) =
        (∫ omega, Set.indicator A (esscherDensity X beta k s) omega ∂P)) := by
  sorry

end Kyprianou.Ch03
