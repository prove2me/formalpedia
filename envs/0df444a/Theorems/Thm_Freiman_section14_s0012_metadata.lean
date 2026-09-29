-- Prove2me | Theorems.Thm_Freiman_section14_s0012_metadata
-- name    : Freiman.section14_s0012_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T03:37:51.842009+00:00
-- url     : https://prove2.me/theorems/5f7519d7-0afd-41de-a1a9-12ff8893bf9b
-- title:
--   Freiman.section14_s0012_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 12).rectangle ∧ 0 ≤ (section14State section14Catalog 12).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 12).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 12)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 12).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_metadata : certRectangleValid (section14State section14Catalog 12).rectangle ∧ 0 ≤ (section14State section14Catalog 12).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 12).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 12)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 12).context).map List.toFinset).toFinset := by sorry
