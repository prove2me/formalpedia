-- Prove2me | Theorems.Thm_OrderHom_map_map_bot_le_lfp
-- name    : OrderHom.map_map_bot_le_lfp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:55:14.764674+00:00
-- url     : https://prove2.me/theorems/f645fc19-c437-45ac-bd19-2b11f18bfccc
-- title:
--   Order Hom: map map bot le lfp
-- statement:
--   **The dual small general order-theoretic fact**, needed for Section 4 below: for *any*
--       monotone `f` on *any* complete lattice, `f (f ⊥) ≤ f.lfp` -- the mirror of
--       `OrderHom.gfp_le_map_map_top` on the `lfp` side, proved the same way with `bot_le`/`map_lfp` in
--       place of `le_top`/`map_gfp`. Where the `gfp` version *upper*-bounds a greatest fixed point by
--       iterating down from `⊤`, this one *lower*-bounds a least fixed point by iterating up from `⊥`
--       -- exactly what showing something is a *member* of a `gfp`-of-`lfp` construction like `LF`
--       needs, dual to Section 3's membership-exclusion argument.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L178-L184
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L178-L184

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true

theorem OrderHom.map_map_bot_le_lfp {α : Type*} [CompleteLattice α] (f : α →o α) :
    f (f ⊥) ≤ f.lfp := by sorry
