-- Prove2me | Theorems.Thm_Kyprianou_Ch02_pointFamilyPrmPartialCountLeV1
-- name    : Kyprianou.Ch02.pointFamilyPrmPartialCountLeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:06:50.043945+00:00
-- url     : https://prove2.me/theorems/b5ebade1-98f3-4f5b-acb1-f7fc8dff395c
-- title:
--   pointFamilyPrmPartialCountLeV1
-- statement:
--   Finite Poisson point-family partial count is dominated pointwise by the full ENNReal random measure evaluation, by the explicit tsum-of-thinned-counts definition and sum_le_tsum.
-- source:
--   Kyprianou (2006), Chapter 2, original PRM existence. Exact LeanLevy.RandomMeasure.PoissonRandomMeasure and PoissonPointFamily source reduction.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem pointFamilyPrmPartialCountLeV1
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (A : Set E) (hA : MeasurableSet A) (n : ℕ) (ω : Ω) :
    (ProbabilityTheory.prmPartialCount K Y A n ω : ENNReal) ≤
      ProbabilityTheory.poissonRandomMeasure K Y ω A := by sorry
end Kyprianou.Ch02
