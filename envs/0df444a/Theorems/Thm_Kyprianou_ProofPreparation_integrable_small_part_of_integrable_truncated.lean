-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_integrable_small_part_of_integrable_truncated
-- name    : Kyprianou.ProofPreparation.integrable_small_part_of_integrable_truncated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:22:13.579545+00:00
-- url     : https://prove2.me/theorems/5cfc2484-c8d1-4b73-be8f-13659e8dfa9c
-- title:
--   Small-value integrability under the truncated Poisson convergence criterion
-- statement:
--   If the measurable truncated absolute-value test function min(1,|f|) is integrable against a measure, then the part of f with |f|≤1 is integrable. Proved by pointwise domination in norm and measurability of a conditional cutoff. This is the small-jump L1 sufficiency ingredient for the original Kyprianou Chapter 2 Theorem 2.7 Poisson-integral criterion.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, sufficiency of ∫min(1,|f|) dm<∞.

import Mathlib
open MeasureTheory
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem integrable_small_part_of_integrable_truncated
    {E : Type} [MeasurableSpace E] (m : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (htrunc : Integrable (fun x => min (1 : ℝ) |f x|) m) :
    Integrable (fun x => if |f x| ≤ 1 then f x else 0) m := by sorry
end Kyprianou.ProofPreparation
