-- Prove2me | Theorems.Thm_OrderHom_lfp_le_of_step
-- name    : OrderHom.lfp_le_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:53:01.92272+00:00
-- url     : https://prove2.me/theorems/aa8bf6d3-df0b-4f18-a4c5-c80ab3110612
-- title:
--   Order Hom: lfp le of step
-- statement:
--   The dual: one step preserves being *above* the least fixed point, so iterating downward from
--       anything above it gives sound upper bounds. For reachability the starting point costs nothing --
--       `f.lfp ≤ ⊤` is `le_top` -- and with nonpositive rewards the constant `0` serves instead, being
--       pre-fixed there.
--
--       Soundness of an upper bound therefore needs no end-component analysis. What such analysis buys
--       is *convergence*: iterating from `⊤` stalls above the value wherever the players can keep the
--       play off the target forever, so the bound stays valid but stops improving.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Lattice.lean#L77-L81
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Lattice.lean#L77-L81

import Mathlib.Order.FixedPoints
import Definitions.Def_Comp_Lattice
set_option autoImplicit true

theorem OrderHom.lfp_le_of_step {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : f.lfp ≤ a) (hb : b = f a) : f.lfp ≤ b := by sorry
