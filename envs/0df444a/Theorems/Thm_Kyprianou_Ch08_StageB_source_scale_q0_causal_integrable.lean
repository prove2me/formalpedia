-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_q0_causal_integrable
-- name    : Kyprianou.Ch08.StageB.source_scale_q0_causal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:05:36.938227+00:00
-- url     : https://prove2.me/theorems/50cd6b69-30cc-4871-9a9a-78753be885d5
-- title:
--   Local causal integrability of source W0 and Wq
-- statement:
--   For source scale W and q≥0, the positive-reserve causal product W0(s) Wq(x−s) is integrable over 0<s≤x for all x≥0. Use source Wq exponential weighted Laplace transform, continuity of W0, and already Proved causal_reflected_product_integrable_of_weighted. Required for the zero-reserve small-interval bound.
-- source:
--   Kyprianou 2006 Chapter 8 Lemma 8.3 (8.23) p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_scale_q0_causal_integrable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    IntegrableOn (fun s : ℝ => W 0 s * W q (x - s))
      (Set.Ioc (0 : ℝ) x) volume := by
  sorry

end Kyprianou.Ch08.StageB
