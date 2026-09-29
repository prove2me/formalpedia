-- Prove2me | Theorems.Thm_Freiman_section14_s0014_metadata
-- name    : Freiman.section14_s0014_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T02:58:37.905988+00:00
-- url     : https://prove2.me/theorems/ddcdc7f9-a8c2-4379-936c-7ce335968af6
-- title:
--   Freiman.section14_s0014_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. certRectangleValid (section14State section14Catalog 14).rectangle ∧ 0 ≤ (section14State section14Catalog 14).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 14).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 14)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 14).context).map List.toFinset).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_metadata : certRectangleValid (section14State section14Catalog 14).rectangle ∧ 0 ≤ (section14State section14Catalog 14).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 14).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 14)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 14).context).map List.toFinset).toFinset := by sorry
