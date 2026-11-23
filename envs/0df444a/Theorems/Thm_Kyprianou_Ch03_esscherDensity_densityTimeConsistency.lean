-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherDensity_densityTimeConsistency
-- name    : Kyprianou.Ch03.esscherDensity_densityTimeConsistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T14:57:15.48262+00:00
-- url     : https://prove2.me/theorems/fc035ebe-d1ba-4be7-a15c-9f71d68f1653
-- title:
--   Esscher exponential density consistency source clause 2
-- statement:
--   Exact independently quantified clause 2 of Esscher exponential density consistency. All original hypotheses and process domains are retained.
-- source:
--   Kyprianou (2006), first edition, Chapter 3, Esscher exponential density consistency

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem esscherDensity_densityTimeConsistency
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
    (∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (∫ omega, Set.indicator A (esscherDensity X beta k t) omega ∂P) =
        (∫ omega, Set.indicator A (esscherDensity X beta k s) omega ∂P)) := by
  sorry

end Kyprianou.Ch03
