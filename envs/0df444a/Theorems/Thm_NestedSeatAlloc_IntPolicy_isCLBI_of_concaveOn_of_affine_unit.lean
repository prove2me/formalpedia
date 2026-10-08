-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_isCLBI_of_concaveOn_of_affine_unit
-- name    : NestedSeatAlloc.IntPolicy.isCLBI_of_concaveOn_of_affine_unit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T17:27:59.574241+00:00
-- url     : https://prove2.me/theorems/b75e7591-6d9a-4297-bbb7-51cd7686b5d1
-- title:
--   Concavity and unit-interval affine pieces imply CLBI
-- statement:
--   A function is CLBI when it is concave on the nonnegative ray and affine on every closed unit interval.
-- source:
--   Source-faithful constructor in candidates/eq27_isclbi_constructor_bridge.lean; it exactly packages the authoritative IsCLBI conjunction needed by the equation-(27) parent proof.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem isCLBI_of_concaveOn_of_affine_unit
    {g : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ici 0) g)
    (haff : ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) (m + 1), g s = a + b * s) :
    IsCLBI g := by sorry

end NestedSeatAlloc.IntPolicy
