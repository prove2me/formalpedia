-- Prove2me | Theorems.Thm_OrderHom_gfp_mono_of_le
-- name    : OrderHom.gfp_mono_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:51:17.457132+00:00
-- url     : https://prove2.me/theorems/bf966f66-74ef-466c-81ab-9bb693d4e206
-- title:
--   Order Hom: gfp mono of le
-- statement:
--   **CSG-independent, dual.** `OrderHom.gfp` is monotone in the operator itself: if `f ≤ g`
--       pointwise, then `f.gfp ≤ g.gfp` -- the exact mirror of `lfp_mono_of_le` via `OrderHom.map_gfp`/
--       `OrderHom.le_gfp`. Not needed by `buchiOp` below (only the `lfp` direction is), but stated
--       alongside it since `co-Büchi`'s solution formula (eq. (5) of the same paper, `μx·νy·(...)`) will
--       need exactly this dual fact for its own outer level, the same way `reachOp`/`safetyOp` are
--       proved as a matched pair.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BuchiOp.lean#L73-L75
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BuchiOp.lean#L73-L75

import Definitions.Def_Csg_CsgMonotone
import Definitions.Def_Csg_BuchiOp
set_option autoImplicit true

theorem OrderHom.gfp_mono_of_le {α : Type*} [CompleteLattice α] {f g : α →o α}
    (h : ∀ a, f a ≤ g a) : f.gfp ≤ g.gfp := by sorry
