-- Prove2me | Theorems.Thm_Kyprianou_Ch04_locallyAffinePathMeasurableV1
-- name    : Kyprianou.Ch04.locallyAffinePathMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:27:38.320363+00:00
-- url     : https://prove2.me/theorems/25de1bb9-84ee-512c-97b6-111ee7816226
-- title:
--   Locally finite affine-step paths are measurable
-- statement:
--   Locally finite affine-step paths are measurable.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem locallyAffinePathMeasurableV1 {ι : Type} (U : NNReal → ℝ)
    (hU : ∀ n : ℕ, ∃ (S : Finset ι) (r a : ι → ℝ) (c d : ℝ),
      ∀ t : NNReal, t ≤ (n : NNReal) →
        U t = c + d * (t : ℝ) + ∑ i ∈ S, if r i ≤ (t : ℝ) then a i else 0) :
    Measurable U := by
  sorry
end Kyprianou.Ch04
