-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherCanonicalGlobalExtension
-- name    : Kyprianou.Ch03.esscherCanonicalGlobalExtension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:07:28.551898+00:00
-- url     : https://prove2.me/theorems/24b018f9-56a9-4313-b32a-cb140d602681
-- title:
--   Global Esscher probability measure on the canonical Lévy path space
-- statement:
--   Constructs a global Esscher probability measure on the canonical coordinate path space, not merely a consistent family of finite-horizon densities. The canonical measurable-space hypothesis justifies extension; this result complements conditional Theorem 3.9.
-- source:
--   Kyprianou (2006), Theorem 3.9 and change of measure discussion, printed pp. 78–80.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem esscherCanonicalGlobalExtension
(P : Measure {path : NNReal → ℝ // path 0 = 0})
    [IsProbabilityMeasure P]
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t omega, X t omega = omega.val t)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : ℝ)
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (beta * x))
      {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    let k := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P);
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0},
      Q Set.univ = 1 ∧
      ∀ (t : NNReal) (A : Set {path : NNReal → ℝ // path 0 = 0}),
        MeasurableSet[PerfCorrMSQ.natFiltr X t] A →
          Q A = ENNReal.ofReal
            (∫ omega, Set.indicator A
              (esscherDensity X beta k t) omega ∂P) := by
  sorry

end Kyprianou.Ch03
