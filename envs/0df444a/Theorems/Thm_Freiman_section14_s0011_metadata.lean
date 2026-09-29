-- Prove2me | Theorems.Thm_Freiman_section14_s0011_metadata
-- name    : Freiman.section14_s0011_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T09:47:00.589804+00:00
-- url     : https://prove2.me/theorems/84f64a36-cab9-49bb-b8e8-0ac51b170ef8
-- title:
--   Freiman.section14_s0011_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 11).rectangle ∧ 0 ≤ (section14State section14Catalog 11).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 11).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 11)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 11).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_metadata : certRectangleValid (section14State section14Catalog 11).rectangle ∧ 0 ≤ (section14State section14Catalog 11).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 11).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 11)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 11).context).map List.toFinset).toFinset := by sorry
