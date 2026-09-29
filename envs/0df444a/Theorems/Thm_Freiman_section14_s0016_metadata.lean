-- Prove2me | Theorems.Thm_Freiman_section14_s0016_metadata
-- name    : Freiman.section14_s0016_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T21:55:53.139657+00:00
-- url     : https://prove2.me/theorems/c8c051b5-3eb5-427a-a83b-324712e51827
-- title:
--   Freiman.section14_s0016_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 16).rectangle ∧ 0 ≤ (section14State section14Catalog 16).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 16).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 16)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 16).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_metadata : certRectangleValid (section14State section14Catalog 16).rectangle ∧ 0 ≤ (section14State section14Catalog 16).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 16).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 16)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 16).context).map List.toFinset).toFinset := by sorry
