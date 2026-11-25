-- Prove2me | Theorems.Thm_OpenMath_induce_isBipartite_iff_exists_coloring
-- name    : OpenMath.induce_isBipartite_iff_exists_coloring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:36:53.826134+00:00
-- url     : https://prove2.me/theorems/ce784355-7d46-413c-b591-4addd1df44e0
-- title:
--   Open Math: induce is Bipartite iff exists coloring
-- statement:
--   An induced subgraph is bipartite exactly when its vertices admit a two-coloring.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean#L54-L64
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean#L54-L64

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
omit [Fintype α]

theorem OpenMath.induce_isBipartite_iff_exists_coloring (G : SimpleGraph α) (s : Finset α) :
    (G.induce s).IsBipartite ↔
      ∃ c : α → Fin 2, ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by sorry
