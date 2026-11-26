-- Prove2me | Theorems.Thm_Kyprianou_Ch04_denseBoundedPrimitiveZero
-- name    : Kyprianou.Ch04.denseBoundedPrimitiveZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:46:17.864136+00:00
-- url     : https://prove2.me/theorems/d340a77a-ffc6-58b9-a1f1-abb939944a9f
-- title:
--   denseBoundedPrimitiveZero
-- statement:
--   A bounded primitive vanishing on a countable dense set vanishes everywhere.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A bounded primitive vanishing on a countable dense set vanishes everywhere. -/
theorem Kyprianou.Ch04.denseBoundedPrimitiveZero (g : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hi : ∀ t : NNReal, IntegrableOn g (Icc (0:ℝ) (t:ℝ)) volume)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0:ℝ)), ‖g r‖ ≤ C)
    (hz : ∀ q : ℕ, (∫ r in Icc (0:ℝ) ((TopologicalSpace.denseSeq NNReal q : NNReal):ℝ), g r ∂volume) = 0) :
    ∀ t : NNReal, (∫ r in Icc (0:ℝ) (t:ℝ), g r ∂volume) = 0 := by
  sorry
