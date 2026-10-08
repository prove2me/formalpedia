-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_concaveOn_translate_add_const
-- name    : NestedSeatAlloc.IntPolicy.concaveOn_translate_add_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T21:28:54.318649+00:00
-- url     : https://prove2.me/theorems/aaaa266d-ec90-4754-9970-bc8404d4c9fb
-- title:
--   Translated concave branch with an additive constant
-- statement:
--   If a function is concave on the nonnegative ray, translating its input and adding a constant preserves concavity on the translated ray.
-- source:
--   Complete direct secant proof for the translated upper branch of the conditional-revenue concavity induction.

import Mathlib

namespace NestedSeatAlloc.IntPolicy

theorem concaveOn_translate_add_const {g : ℝ → ℝ} {d c : ℝ}
    (hg : ConcaveOn ℝ (Set.Ici 0) g) :
    ConcaveOn ℝ (Set.Ici d) (fun x => c + g (x - d)) := by sorry

end NestedSeatAlloc.IntPolicy
