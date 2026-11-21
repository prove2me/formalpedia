-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_causal_reflected_product_integrable_of_weighted
-- name    : Kyprianou.Ch08.StageB.causal_reflected_product_integrable_of_weighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:12:50.473179+00:00
-- url     : https://prove2.me/theorems/80c6d17e-b41c-43c5-8d56-795626019652
-- title:
--   Weighted halfline integrability of a compact causal convolution integrand
-- statement:
--   A globally exponentially weighted integrable kernel f, reflected on 0≤s≤x, can be multiplied by a continuous scale kernel g on [0,x] without losing integrability. Derive this from the exact reflected-Ioc integrability lemma, multiplication by a compact-continuous exponential factor and the cancellation of exp(±β(x−s)). This supplies source-accurate q-scale power local integrability required by Kyprianou Lemma 8.3.
-- source:
--   Weighted convolution change of variables used in Kyprianou (2006) Lemma 8.3 (8.23), printed p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory Set

namespace Kyprianou.Ch08.StageB

/-- Compact causal products inherit integrability from a weighted half-line kernel. -/
theorem causal_reflected_product_integrable_of_weighted
    (f g : ℝ → ℝ) (β x : ℝ) (hx : 0 ≤ x)
    (hf : IntegrableOn (fun t : ℝ => Real.exp (-(β * t)) * f t)
      (Set.Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ))) :
    IntegrableOn (fun s : ℝ => g s * f (x - s))
      (Set.Ioc (0 : ℝ) x) volume := by
  sorry

end Kyprianou.Ch08.StageB
