-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherDensityUnit_integrability
-- name    : Kyprianou.Ch03.esscherDensityUnit_integrability
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T15:00:14.408926+00:00
-- url     : https://prove2.me/theorems/435eff69-7b17-42cb-ac04-73affb53e7e3
-- title:
--   Esscher density integrability and normalisation clause 1
-- statement:
--   Independent full-strength integrability clause preserving all the original quantified assumptions and process models.
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

theorem esscherDensityUnit_integrability
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
Integrable (esscherDensity X beta k t) P) := by
  sorry

end Kyprianou.Ch03
