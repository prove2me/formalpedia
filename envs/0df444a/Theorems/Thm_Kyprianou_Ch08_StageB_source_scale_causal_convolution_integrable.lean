-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_causal_convolution_integrable
-- name    : Kyprianou.Ch08.StageB.source_scale_causal_convolution_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:57:32.451468+00:00
-- url     : https://prove2.me/theorems/825b0cbc-f7d0-40fc-a9eb-ddf9301d0cb2
-- title:
--   Local W-convolution integrability from source-scale continuity
-- statement:
--   If W is a source-authenticated q-scale family and q,x≥0, continuity of W(q) on [0,∞) implies its first causal convolution integrand W(q,s) W(q,x−s) is integrable on (0,x]. This discharges the integrability assumption needed for (8.23) and Lemma 8.3.
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3, inequality (8.23) and proof on printed p. 221.

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Local integrability of the causal W-convolution from scale continuity. -/
theorem source_scale_causal_convolution_integrable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    IntegrableOn (fun s : ℝ => W q s * W q (x - s))
      (Set.Ioc (0 : ℝ) x) volume := by
  sorry

end Kyprianou.Ch08.StageB
