-- Prove2me | Theorems.Thm_Freiman_section14_s0013_metadata
-- name    : Freiman.section14_s0013_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T09:34:54.277058+00:00
-- url     : https://prove2.me/theorems/aaf3a082-e6e1-4db7-a6e6-f60a40362da4
-- title:
--   Freiman.section14_s0013_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 13).rectangle ∧ 0 ≤ (section14State section14Catalog 13).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 13).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 13)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 13).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_metadata : certRectangleValid (section14State section14Catalog 13).rectangle ∧ 0 ≤ (section14State section14Catalog 13).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 13).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 13)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 13).context).map List.toFinset).toFinset := by sorry
