-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_metadata
-- name    : Freiman.workReverse20260919_s0001_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T20:01:32.263534+00:00
-- url     : https://prove2.me/theorems/6778aeee-938d-49e1-947e-1556c31afda4
-- title:
--   Freiman.workReverse20260919_s0001_metadata
-- statement:
--   The exact original plan metadata and all endpoint specifications in the indicated slice are verified using the original catalogue and endpoint formulae.
--
--   certRectangleValid (section14State section14Catalog 1).rectangle ∧ 0 ≤ (section14State section14Catalog 1).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 1).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 1)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 1).context).map List.toFinset).toFinset
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_metadata : certRectangleValid (section14State section14Catalog 1).rectangle ∧ 0 ≤ (section14State section14Catalog 1).rectangle.r0 ∧ 0 ≤ (section14State section14Catalog 1).rectangle.s0 ∧ ((section14Parents section14Catalog (section14State section14Catalog 1)).map (fun p => (section14Bounds section14Catalog p.conditions).toFinset)).toFinset = ((section14ExpectedParents (section14State section14Catalog 1).context).map List.toFinset).toFinset := by sorry
