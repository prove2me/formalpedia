-- Prove2me | Theorems.Thm_LocalLemma_exp_regular_bound
-- name    : LocalLemma.exp_regular_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:21:30.64499+00:00
-- url     : https://prove2.me/theorems/bafb8b43-1963-4d31-a135-f435c5f36647
-- title:
--   Local Lemma: exp regular bound
-- statement:
--   `e (k (k - 1) + 1) ≤ 2 ^ (k - 1)` for `k ≥ 9`.
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L417-L435
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L417-L435

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma

theorem LocalLemma.exp_regular_bound (k : ℕ) (hk : 9 ≤ k) :
    Real.exp 1 * (((k * (k - 1) : ℕ) : ℝ) + 1) ≤ 2 ^ (k - 1) := by sorry
