-- Prove2me | Theorems.Thm_GJKKL_sum_card_le_card_biUnion_add
-- name    : GJKKL.sum_card_le_card_biUnion_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:00.74456+00:00
-- url     : https://prove2.me/theorems/2cc8f110-602f-44b7-8069-0b38a7f74413
-- title:
--   GJKKL: sum card le card bi Union add
-- statement:
--   Bonferroni: `Σ_i |S_i| ≤ |⋃ S_i| + Σ_i Σ_{j ≠ i} |S_i ∩ S_j|`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L31-L45
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L31-L45

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom

theorem GJKKL.sum_card_le_card_biUnion_add {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (s : Finset ι) (S : ι → Finset β) :
    ∑ i ∈ s, (S i).card ≤
      (s.biUnion S).card + ∑ i ∈ s, ∑ j ∈ s.erase i, (S i ∩ S j).card := by sorry
