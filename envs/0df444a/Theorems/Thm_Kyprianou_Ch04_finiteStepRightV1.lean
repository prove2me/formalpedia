-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteStepRightV1
-- name    : Kyprianou.Ch04.finiteStepRightV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:51:45.257091+00:00
-- url     : https://prove2.me/theorems/1dd86b1e-2b96-4100-93c0-5eae53294343
-- title:
--   Right continuity of paths with compact finite-step representations
-- statement:
--   Right continuity of paths with compact finite-step representations
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteStepRightV1 {ι : Type} (U : NNReal → ℝ)
    (hU : ∀ n : ℕ, ∃ (s : Finset ι) (r a : ι → ℝ),
      ∀ t : NNReal, t ≤ (n : NNReal) →
        U t = ∑ i ∈ s, if r i ≤ (t : ℝ) then a i else 0) :
    ∀ t : NNReal, Tendsto U (𝓝[>] t) (𝓝 (U t)) := by
  sorry
end Kyprianou.Ch04
