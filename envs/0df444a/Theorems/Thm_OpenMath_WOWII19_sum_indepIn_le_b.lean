-- Prove2me | Theorems.Thm_OpenMath_WOWII19_sum_indepIn_le_b
-- name    : OpenMath.WOWII19.sum_indepIn_le_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:12.565331+00:00
-- url     : https://prove2.me/theorems/7b91c9bd-7789-55c8-90c8-9ca033eaca5d
-- title:
--   WOWII19: sum indep In le b
-- statement:
--   **Layer lemma**: `b(G) ≥ ∑_{i ≤ e} α(L_i(v))`.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L116-L142
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L116-L142

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OpenMath.WOWII19.sum_indepIn_le_b (G : SimpleGraph α) (v : α) (e : ℕ) :
    ∑ i ∈ range (e + 1), indepIn G (layer G v i) ≤ largestInducedBipartiteSubgraphSize G := by sorry
