-- Prove2me | Theorems.Thm_OpenMath_WOWII19_bound_two
-- name    : OpenMath.WOWII19.bound_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:31.75058+00:00
-- url     : https://prove2.me/theorems/b73b6c8a-1ccc-56fa-8834-4462a1aeb38b
-- title:
--   WOWII19: bound two
-- statement:
--   **Bound 2**: if `d(x, y) = D` and `d(v, x) ≤ d(v, y)`, then `b ≥ l(v) + D − 1`.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L180-L258
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L180-L258

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
variable {G : SimpleGraph α}

theorem OpenMath.WOWII19.bound_two (h : G.Connected) (v x y : α) (D : ℕ) (hxy : G.dist x y = D)
    (hav : G.dist v x ≤ G.dist v y) (he : 1 ≤ ecc G v) :
    indepNeighborsCard G v + D ≤ largestInducedBipartiteSubgraphSize G + 1 := by sorry
