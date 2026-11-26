-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedPrimitiveLipschitzV1
-- name    : Kyprianou.Ch04.boundedPrimitiveLipschitzV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:26:08.813629+00:00
-- url     : https://prove2.me/theorems/729db496-2dc7-4af0-a388-40f7c6b6a74d
-- title:
--   Lipschitz estimate for bounded measurable time primitives
-- statement:
--   Lipschitz estimate for bounded measurable time primitives
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedPrimitiveLipschitzV1 (g : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ s : ℝ, 0 ≤ s → |g s| ≤ C) :
    ∀ u v : NNReal, u ≤ v →
      |(∫ s in Icc (0 : ℝ) (v : ℝ), g s ∂volume) -
        (∫ s in Icc (0 : ℝ) (u : ℝ), g s ∂volume)| ≤
        C * ((v : ℝ) - (u : ℝ)) := by
  sorry
end Kyprianou.Ch04
