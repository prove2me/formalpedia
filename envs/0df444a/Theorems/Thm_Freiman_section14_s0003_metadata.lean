-- Prove2me | Theorems.Thm_Freiman_section14_s0003_metadata
-- name    : Freiman.section14_s0003_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:46:34.501589+00:00
-- url     : https://prove2.me/theorems/3601c774-9904-446b-8b2f-2130d88ebe0f
-- title:
--   Freiman.section14_s0003_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 3).rectangle ∧ 0 ≤ (section14State section14Catalog 3).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 3).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 3)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 3).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_metadata : certRectangleValid (section14State section14Catalog 3).rectangle ∧ 0 ≤ (section14State section14Catalog 3).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 3).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 3)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 3).context).map List.toFinset).toFinset := by sorry
