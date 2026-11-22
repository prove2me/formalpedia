-- Prove2me | Theorems.Thm_GridHam_chain_proj_intermediate
-- name    : GridHam.chain_proj_intermediate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:47:50.84432+00:00
-- url     : https://prove2.me/theorems/720d95de-5470-4527-a412-e3aace4c6352
-- title:
--   Grid Ham: chain proj intermediate
-- statement:
--   Intermediate values along an adjacent-chain, for any coordinate-like `f`
--   that changes by at most 1 per grid step.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L33-L84
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L33-L84

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chain_proj_intermediate (f : Coord → ℕ)
    (hf : ∀ a b, Adjacent a b → f a ≤ f b + 1 ∧ f b ≤ f a + 1) :
    ∀ (l : List Coord), chainAdjacent l = true →
      ∀ a ∈ l, ∀ b ∈ l, ∀ z, f a ≤ z → z ≤ f b → ∃ c ∈ l, f c = z := by sorry
