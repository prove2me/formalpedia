-- Prove2me | Theorems.Thm_OrderHom_eq_lfp_of_fixed_of_le
-- name    : OrderHom.eq_lfp_of_fixed_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:23.443183+00:00
-- url     : https://prove2.me/theorems/f1434839-9bed-4fb2-a19e-8a235f0884be
-- title:
--   Order Hom: eq lfp of fixed of le
-- statement:
--   A fixed point that is also below `f.lfp` *is* `f.lfp`. The second hypothesis is what an iterate
--       from `⊥` supplies (`OrderHom.le_lfp_of_step`); the first is a decidable check on a finite
--       lattice. Together they pin a least fixed point exactly, with no minimality argument and no
--       bound on how many steps stabilisation takes.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Lattice.lean#L37-L39
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Lattice.lean#L37-L39

import Mathlib.Order.FixedPoints
import Definitions.Def_Comp_Lattice
set_option autoImplicit true

theorem OrderHom.eq_lfp_of_fixed_of_le {α : Type*} [CompleteLattice α] (f : α →o α) {a : α}
    (hfix : f a = a) (hle : a ≤ f.lfp) : a = f.lfp := by sorry
