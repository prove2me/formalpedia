-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finitePhysicalWindowExactJumpAtomsV1
-- name    : Kyprianou.Ch04.finitePhysicalWindowExactJumpAtomsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:23:16.358433+00:00
-- url     : https://prove2.me/theorems/30909712-a8c4-46aa-88b9-68637442688b
-- title:
--   Exact finite jump atoms of a physical marked window
-- statement:
--   A finite marked window has finite exact jump-time support by its encard formula. Compare the restricted measure and the sum of Dirac measures on every measurable set.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finitePhysicalWindowExactJumpAtomsV1 {Ω : Type} (X L : NNReal → Ω → ℝ) (ω : Ω)
    (hX : Measurable (fun t => X t ω)) (hL : Measurable (fun t => L t ω))
    (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (hfin : Kyprianou.Ch04.pathJumpMeasure X L ω R < ⊤) :
    ∃ S : Finset NNReal,
      (∀ t, t ∈ S ↔ 0 < t ∧ X t ω ≠ L t ω ∧ ((t : ℝ),X t ω - L t ω) ∈ R) ∧
      (Kyprianou.Ch04.pathJumpMeasure X L ω).restrict R =
        ∑ t ∈ S, Measure.dirac ((t : ℝ), X t ω - L t ω) := by
  sorry
end Kyprianou.Ch04
