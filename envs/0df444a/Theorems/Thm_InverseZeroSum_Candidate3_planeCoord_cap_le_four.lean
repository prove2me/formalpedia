-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_planeCoord_cap_le_four
-- name    : InverseZeroSum.Candidate3.planeCoord_cap_le_four
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:27:09.617511+00:00
-- url     : https://prove2.me/theorems/e621600d-1642-45d9-86fc-138769ff456a
-- title:
--   Candidate3: plane Coord cap le four
-- statement:
--   The small affine-plane fact needed by S045: a subset of \`F_3^2\` with no
--   three distinct elements summing to zero has at most four elements.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L437-L444
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L437-L444

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.planeCoord_cap_le_four :
    ∀ A : Finset PlaneCoord,
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ≠ b → a ≠ c → b ≠ c → a + b + c ≠ 0) →
      A.card ≤ 4 := by sorry
