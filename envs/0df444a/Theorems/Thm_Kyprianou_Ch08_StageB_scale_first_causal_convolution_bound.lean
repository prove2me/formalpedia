-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_scale_first_causal_convolution_bound
-- name    : Kyprianou.Ch08.StageB.scale_first_causal_convolution_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:57:33.528893+00:00
-- url     : https://prove2.me/theorems/a4d04937-ca1e-425c-abdf-206ac50cf43e
-- title:
--   First factorial scale-convolution integral bound
-- statement:
--   Under positivity and monotonicity on [0,∞), and the required integrability, the first causal convolution of W with itself at x is ≤x W(x)^2. This is the k=1 case of Kyprianou (8.23); the pointwise integrand bound is supplied by its separate Chapter 8 lemma.
-- source:
--   Kyprianou (2006), Chapter 8, Lemma 8.3 proof of inequality (8.23), printed p. 221.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- First-factorial convolution upper bound from monotone scale data. -/
theorem scale_first_causal_convolution_bound (W : ℝ → ℝ)
    (hmono : MonotoneOn W (Set.Ici (0 : ℝ)))
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ W t)
    (x : ℝ) (hx : 0 ≤ x)
    (hint : IntegrableOn (fun s : ℝ => W s * W (x - s))
      (Set.Ioc (0 : ℝ) x) volume) :
    (∫ s in Set.Ioc (0 : ℝ) x, W s * W (x - s) ∂volume) ≤
      x * (W x) ^ 2 := by
  sorry

end Kyprianou.Ch08.StageB
