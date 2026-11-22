-- Prove2me | Theorems.Thm_OrderHom_le_lfp_of_step
-- name    : OrderHom.le_lfp_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:24.572772+00:00
-- url     : https://prove2.me/theorems/1ed6ed8c-4d95-4b4e-9303-db2b66671661
-- title:
--   Order Hom: le lfp of step
-- statement:
--   One step preserves being below the least fixed point: a monotone map sends anything `≤ f.lfp`
--       to something `≤ f.lfp`, because `f.lfp` is a fixed point (`OrderHom.map_lfp`). Stated with the
--       step as an equation `b = f a` so that it composes directly with a certified computation, which
--       produces `b` and a proof that it is what `f` returned.
--
--       Declared at top level in the `OrderHom` namespace, following
--       `Csg/IntervalCertificate.lean`'s own lattice-level lemmas.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Lattice.lean#L63-L67
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Lattice.lean#L63-L67

import Mathlib.Order.FixedPoints
import Definitions.Def_Comp_Lattice
set_option autoImplicit true

theorem OrderHom.le_lfp_of_step {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : a ≤ f.lfp) (hb : b = f a) : b ≤ f.lfp := by sorry
