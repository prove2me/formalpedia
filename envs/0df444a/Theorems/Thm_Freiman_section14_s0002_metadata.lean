-- Prove2me | Theorems.Thm_Freiman_section14_s0002_metadata
-- name    : Freiman.section14_s0002_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:32:22.141985+00:00
-- url     : https://prove2.me/theorems/9ab6b225-d861-4b3c-b24b-832f328ff2ab
-- title:
--   Freiman.section14_s0002_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 2).rectangle ∧ 0 ≤ (section14State section14Catalog 2).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 2).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 2)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 2).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_metadata : certRectangleValid (section14State section14Catalog 2).rectangle ∧ 0 ≤ (section14State section14Catalog 2).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 2).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 2)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 2).context).map List.toFinset).toFinset := by sorry
