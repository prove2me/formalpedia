-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherDensityUnit_unitMean
-- name    : Kyprianou.Ch03.esscherDensityUnit_unitMean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:00:19.842757+00:00
-- url     : https://prove2.me/theorems/f54dc242-1aeb-4d84-a4f3-3e6ad7e7a7fc
-- title:
--   Esscher density integrability and normalisation clause 2
-- statement:
--   Independent full-strength unitMean clause preserving all the original quantified assumptions and process models.
-- source:
--   Kyprianou (2006), first edition, Chapter 3, Esscher density integrability and normalisation

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem esscherDensityUnit_unitMean
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
(∫ omega, esscherDensity X beta k t omega ∂P) = 1) := by
  sorry

end Kyprianou.Ch03
