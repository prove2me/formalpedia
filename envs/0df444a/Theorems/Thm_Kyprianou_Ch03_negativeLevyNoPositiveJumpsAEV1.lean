-- Prove2me | Theorems.Thm_Kyprianou_Ch03_negativeLevyNoPositiveJumpsAEV1
-- name    : Kyprianou.Ch03.negativeLevyNoPositiveJumpsAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:00:29.006972+00:00
-- url     : https://prove2.me/theorems/4d8dab1b-74a3-4009-b377-8a3987c46dbe
-- title:
--   Negative Lévy measure implies almost-sure absence of positive jumps
-- statement:
--   Identify the law of the large positive jump counting process, use zero intensity for positive bands and a countable exhaustion of time and jump size. The statement concerns the original process, simultaneously over all times.
-- source:
--   Kyprianou (2006), Chapters 2–3; reduction of 063b9d7c-87f6-432a-91c5-8ca8556a76f0.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.negativeLevyNoPositiveJumpsAEV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (hNegative : T.levyMeasure (Set.Ici (0 : ℝ)) = 0) :
    ∀ᵐ omega ∂P, ∀ (t : NNReal) (l : ℝ), 0 < t →
      Tendsto (fun s => X s omega) (nhdsWithin t (Iio t)) (nhds l) →
      X t omega ≤ l := by
  sorry
