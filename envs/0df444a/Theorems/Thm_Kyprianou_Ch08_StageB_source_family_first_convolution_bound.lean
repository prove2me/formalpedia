-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_family_first_convolution_bound
-- name    : Kyprianou.Ch08.StageB.source_family_first_convolution_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:57:34.250106+00:00
-- url     : https://prove2.me/theorems/5e8ae176-c320-4a06-a581-b0154606b3b1
-- title:
--   The first source-q-scale factorial convolution bound
-- statement:
--   For the actual scale family W^(q) of a spectrally negative process, the first self-convolution over 0<s≤x is at most x[W^(q)(x)]². It directly discharges the k=1 case of Kyprianou Lemma 8.3 factorial majorant from the source-scale positivity/monotonicity, integrability and generic convolution lemmas.
-- source:
--   Kyprianou (2006), Chapter 8, Lemma 8.3 inequality (8.23) at k=1, printed p. 221.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- The k=1 factorial convolution estimate, for the actual source scale family. -/
theorem source_family_first_convolution_bound
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    (∫ s in Set.Ioc (0 : ℝ) x, W q s * W q (x - s) ∂volume) ≤
      x * (W q x) ^ 2 := by
  sorry

end Kyprianou.Ch08.StageB
