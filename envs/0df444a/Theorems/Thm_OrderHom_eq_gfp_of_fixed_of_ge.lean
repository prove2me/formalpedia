-- Prove2me | Theorems.Thm_OrderHom_eq_gfp_of_fixed_of_ge
-- name    : OrderHom.eq_gfp_of_fixed_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:44:37.593795+00:00
-- url     : https://prove2.me/theorems/8b53a815-6c72-47f6-b597-4e53296d5fe3
-- title:
--   Order Hom: eq gfp of fixed of ge
-- statement:
--   The dual: a fixed point that is also above `f.gfp` *is* `f.gfp`, the second hypothesis coming
--       from an iterate downward from `⊤`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Lattice.lean#L43-L45
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Lattice.lean#L43-L45

import Mathlib.Order.FixedPoints
import Definitions.Def_Comp_Lattice
set_option autoImplicit true

theorem OrderHom.eq_gfp_of_fixed_of_ge {α : Type*} [CompleteLattice α] (f : α →o α) {a : α}
    (hfix : f a = a) (hge : f.gfp ≤ a) : a = f.gfp := by sorry
