-- Prove2me | Theorems.Thm_OrderHom_gfp_le_map_map_top
-- name    : OrderHom.gfp_le_map_map_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:59:37.386018+00:00
-- url     : https://prove2.me/theorems/92271e12-c1d0-48c1-8f58-fd326391a5ce
-- title:
--   Order Hom: gfp le map map top
-- statement:
--   **A small general order-theoretic fact**, not specific to `CSG`/`Skirmish` at all: for *any*
--       monotone `f` on *any* complete lattice, `f.gfp ≤ f (f ⊤)` -- no `ωScottContinuous`/continuity
--       hypothesis needed, unlike the general Kleene-style characterisation
--       (`OrderHom.gfp_eq_sInf_iterate`). Proof: `f.gfp ≤ ⊤` trivially, so by monotonicity
--       `f (f.gfp) ≤ f ⊤`, and `f (f.gfp) = f.gfp` (`map_gfp`) turns this into `f.gfp ≤ f ⊤`; apply `f`
--       (monotone) once more and use `map_gfp` again to get `f.gfp ≤ f (f ⊤)`. Kept local to this file
--       since its only use here is bounding `AF`/`AFOuter` from above by two hand-computed steps rather
--       than needing the exact fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L163-L169
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L163-L169

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true

theorem OrderHom.gfp_le_map_map_top {α : Type*} [CompleteLattice α] (f : α →o α) :
    f.gfp ≤ f (f ⊤) := by sorry
