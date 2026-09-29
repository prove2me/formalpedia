-- Prove2me | Theorems.Thm_Freiman_section14_s0008_metadata
-- name    : Freiman.section14_s0008_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T06:09:39.853989+00:00
-- url     : https://prove2.me/theorems/a73d8460-f78f-414c-8ffb-1ea5f0469498
-- title:
--   Freiman.section14_s0008_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 8).rectangle ∧ 0 ≤ (section14State section14Catalog 8).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 8).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 8)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 8).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_metadata : certRectangleValid (section14State section14Catalog 8).rectangle ∧ 0 ≤ (section14State section14Catalog 8).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 8).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 8)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 8).context).map List.toFinset).toFinset := by sorry
