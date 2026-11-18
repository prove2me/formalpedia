-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_measure_large_values_lt_top_of_integrable_truncated
-- name    : Kyprianou.ProofPreparation.measure_large_values_lt_top_of_integrable_truncated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:23:17.155319+00:00
-- url     : https://prove2.me/theorems/88a3384c-a365-44a7-a10b-c7164dd2bdbf
-- title:
--   Finite intensity of marks above unit magnitude under truncated Poisson integrability
-- statement:
--   For measurable real f, if min(1,|f|) is integrable with respect to the intensity measure, then the large-value region {x: 1 < |f(x)|} has finite intensity. On that region, min(1,|f|)=1. Domination gives integrability of its constant-one indicator, and the pinned integrableOn_const_iff shows its measure is finite. This is the large-jump finite-activity half of the original Kyprianou Chapter 2 Theorem 2.7 integrability criterion.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, finite activity of |f|>1 under ∫min(1,|f|)dm<∞.

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem measure_large_values_lt_top_of_integrable_truncated
    {E : Type} [MeasurableSpace E] (m : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (htrunc : Integrable (fun x => min (1 : ℝ) |f x|) m) :
    m {x | 1 < |f x|} < ⊤ := by sorry
end Kyprianou.ProofPreparation
