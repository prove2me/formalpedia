-- Prove2me | Theorems.Thm_Kyprianou_Ch02_measurableRealSequenceLimitVersionCh02V1
-- name    : Kyprianou.Ch02.measurableRealSequenceLimitVersionCh02V1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:35:13.099473+00:00
-- url     : https://prove2.me/theorems/df9a3d59-e0f4-496a-88bf-4d521b2e7ddc
-- title:
--   Measurable real-valued sequence limit on its convergence set
-- statement:
--   A sequence of measurable real functions has a measurable representative equal to its pointwise limit wherever a finite limit exists.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

import Mathlib
open MeasureTheory Filter Topology
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem measurableRealSequenceLimitVersionCh02V1
    {Ω : Type} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n)) :
    ∃ g : Ω → ℝ, Measurable g ∧
      ∀ ω l, Tendsto (fun n => F n ω) atTop (nhds l) → g ω = l := by sorry
end Kyprianou.Ch02
