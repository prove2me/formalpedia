-- Prove2me | Theorems.Thm_OpenMath_exists_parent
-- name    : OpenMath.exists_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:36:54.015979+00:00
-- url     : https://prove2.me/theorems/c4c79f89-a436-4dd1-8912-5bd66ffa9f14
-- title:
--   Open Math: exists parent
-- statement:
--   In a connected graph every vertex `w ≠ v` has a neighbour one step closer to `v`.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean#L69-L79
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean#L69-L79

module
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Real.Basic
public import Definitions.Def_OpenMath_Common
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath
open SimpleGraph Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OpenMath.exists_parent {G : SimpleGraph α} (h : G.Connected) {v w : α} (hw : w ≠ v) :
    ∃ p, G.Adj p w ∧ G.dist v p + 1 = G.dist v w := by sorry
