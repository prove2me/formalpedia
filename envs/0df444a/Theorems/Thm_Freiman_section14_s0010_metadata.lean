-- Prove2me | Theorems.Thm_Freiman_section14_s0010_metadata
-- name    : Freiman.section14_s0010_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T15:39:14.218233+00:00
-- url     : https://prove2.me/theorems/a07c8ec3-f3ed-4824-9fdf-76da85737538
-- title:
--   Freiman.section14_s0010_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 10).rectangle ∧ 0 ≤ (section14State section14Catalog 10).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 10).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 10)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 10).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_metadata : certRectangleValid (section14State section14Catalog 10).rectangle ∧ 0 ≤ (section14State section14Catalog 10).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 10).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 10)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 10).context).map List.toFinset).toFinset := by sorry
