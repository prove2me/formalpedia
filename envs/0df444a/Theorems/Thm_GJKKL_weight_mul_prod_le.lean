-- Prove2me | Theorems.Thm_GJKKL_weight_mul_prod_le
-- name    : GJKKL.weight_mul_prod_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:41.08634+00:00
-- url     : https://prove2.me/theorems/2f7b25ef-7a3a-44c4-80de-c482673070d4
-- title:
--   GJKKL: weight mul prod le
-- statement:
--   On `T*`, the probability of a history is at most `∏ 1/g i`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Counting.lean#L36-L54
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Counting.lean#L36-L54

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Greedy_Counting
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.weight_mul_prod_le (H : Finset (Finset V)) (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∀ h : List (Finset V), ManyAvail H g h →
      weight (greedyKernel H) h * ∏ i ∈ range h.length, g i ≤ 1
  := by sorry
