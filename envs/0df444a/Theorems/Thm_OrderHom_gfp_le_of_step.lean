-- Prove2me | Theorems.Thm_OrderHom_gfp_le_of_step
-- name    : OrderHom.gfp_le_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:45:34.530635+00:00
-- url     : https://prove2.me/theorems/2a936e25-ea3b-4253-9075-3b130419c16d
-- title:
--   Order Hom: gfp le of step
-- statement:
--   One step preserves being above the greatest fixed point, so iterating down from `⊤` gives a
--       chain of upper bounds on a `gfp`. The mirror of `Comp/Reach.lean`'s `OrderHom.le_lfp_of_step`,
--       and what supplies `eq_gfp_of_fixed_of_ge`'s second hypothesis.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Lattice.lean#L50-L54
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Lattice.lean#L50-L54

import Mathlib.Order.FixedPoints
import Definitions.Def_Comp_Lattice
set_option autoImplicit true

theorem OrderHom.gfp_le_of_step {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : f.gfp ≤ a) (hb : b = f a) : f.gfp ≤ b := by sorry
