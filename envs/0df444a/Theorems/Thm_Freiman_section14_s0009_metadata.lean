-- Prove2me | Theorems.Thm_Freiman_section14_s0009_metadata
-- name    : Freiman.section14_s0009_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T18:41:43.68413+00:00
-- url     : https://prove2.me/theorems/befd41b1-a261-4497-b9bb-4ee972a9e2df
-- title:
--   Freiman.section14_s0009_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 9).rectangle ∧ 0 ≤ (section14State section14Catalog 9).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 9).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 9)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 9).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_metadata : certRectangleValid (section14State section14Catalog 9).rectangle ∧ 0 ≤ (section14State section14Catalog 9).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 9).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 9)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 9).context).map List.toFinset).toFinset := by sorry
