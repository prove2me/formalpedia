-- Prove2me | Theorems.Thm_Freiman_section14_s0007_metadata
-- name    : Freiman.section14_s0007_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:41:49.479539+00:00
-- url     : https://prove2.me/theorems/f722bd3e-09e1-482d-9fff-3e42de657b29
-- title:
--   Freiman.section14_s0007_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 7).rectangle ∧ 0 ≤ (section14State section14Catalog 7).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 7).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 7)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 7).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_metadata : certRectangleValid (section14State section14Catalog 7).rectangle ∧ 0 ≤ (section14State section14Catalog 7).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 7).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 7)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 7).context).map List.toFinset).toFinset := by sorry
