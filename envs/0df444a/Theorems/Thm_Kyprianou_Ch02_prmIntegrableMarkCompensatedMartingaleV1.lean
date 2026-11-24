-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmIntegrableMarkCompensatedMartingaleV1
-- name    : Kyprianou.Ch02.prmIntegrableMarkCompensatedMartingaleV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:20:54.787432+00:00
-- url     : https://prove2.me/theorems/cf1997aa-ddd2-409a-b6cd-4c701c281c95
-- title:
--   Completed natural-filtration martingale for any integrable deterministic mark function
-- statement:
--   Integrable compensated deterministic marks over the full jump region on the same completed right-continuous Poisson filtration. Prove using finite-intensity truncation and simple marks, Campbell L1 control, independence of future increments from past, and martingale closure; no L2 premise.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.6 and worked solution; current corrected V3 parent 2d7732b0-159a-41c5-9727-2eb4777ea9df.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem prmIntegrableMarkCompensatedMartingaleV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f ν) :
    ∃ ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
      Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ ∧
      MeasureTheory.Martingale
        (fun (t : ℝ≥0) ω =>
          (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
              f z.2 ∂(N.N ω)) -
          (t : ℝ) * ∫ x, f x ∂ν) ℱ P := by sorry

end Kyprianou.Ch02
