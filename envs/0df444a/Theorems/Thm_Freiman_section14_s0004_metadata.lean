-- Prove2me | Theorems.Thm_Freiman_section14_s0004_metadata
-- name    : Freiman.section14_s0004_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T01:28:05.907774+00:00
-- url     : https://prove2.me/theorems/c3debd76-f920-483f-8062-9e078f1a8c99
-- title:
--   Freiman.section14_s0004_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 4).rectangle ∧ 0 ≤ (section14State section14Catalog 4).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 4).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 4)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 4).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_metadata : certRectangleValid (section14State section14Catalog 4).rectangle ∧ 0 ≤ (section14State section14Catalog 4).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 4).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 4)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 4).context).map List.toFinset).toFinset := by sorry
