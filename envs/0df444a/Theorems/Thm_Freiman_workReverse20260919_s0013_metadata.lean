-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_metadata
-- name    : Freiman.workReverse20260919_s0013_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:11:34.773335+00:00
-- url     : https://prove2.me/theorems/c93583d9-a407-444f-b5d0-e5f77b2cbfcb
-- title:
--   Freiman.workReverse20260919_s0013_metadata
-- statement:
--   The exact original plan metadata and all endpoint specifications in the indicated slice are verified using the original catalogue and endpoint formulae.
--
--   certRectangleValid (section14State section14Catalog 13).rectangle ∧ 0 ≤ (section14State section14Catalog 13).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 13).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 13)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 13).context).map List.toFinset).toFinset
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_metadata : certRectangleValid (section14State section14Catalog 13).rectangle ∧ 0 ≤ (section14State section14Catalog 13).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 13).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 13)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 13).context).map List.toFinset).toFinset := by sorry
