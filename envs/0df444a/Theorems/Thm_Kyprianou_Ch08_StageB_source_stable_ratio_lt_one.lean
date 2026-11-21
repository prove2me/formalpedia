-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_ratio_lt_one
-- name    : Kyprianou.Ch08.StageB.source_stable_ratio_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:31:17.791668+00:00
-- url     : https://prove2.me/theorems/f66c8387-b1b5-4219-9df7-8e430bf95b41
-- title:
--   Spectrally negative stable q-scale geometric ratio below one
-- statement:
--   For α>1, q>0 and β>q^(1/α), the discount ratio q/β^α lies in [0,1). Use monotonicity of Real.rpow for positive exponent and (q^(1/α))^α=q. This is the analytic convergence hypothesis for the stable integrated scale Laplace series in Kyprianou Chapter 8 Exercise 8.2(i).
-- source:
--   Kyprianou (2006) Chapter 8 Exercise 8.2(i).

import Mathlib
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
theorem source_stable_ratio_lt_one
    (α q β : ℝ) (hα : 1 < α) (hq : 0 < q)
    (hβ : q ^ (1 / α) < β) :
    0 ≤ q / β ^ α ∧ q / β ^ α < 1 := by
  sorry
end Kyprianou.Ch08.StageB
