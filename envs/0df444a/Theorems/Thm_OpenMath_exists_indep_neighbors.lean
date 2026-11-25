-- Prove2me | Theorems.Thm_OpenMath_exists_indep_neighbors
-- name    : OpenMath.exists_indep_neighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:37:02.896816+00:00
-- url     : https://prove2.me/theorems/7f42213a-71cb-562b-a556-af1a32111416
-- title:
--   Open Math: exists indep neighbors
-- statement:
--   A maximum independent set of the neighbourhood of `u`, as a `Finset α`.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean#L137-L153
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean#L137-L153

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

theorem OpenMath.exists_indep_neighbors (G : SimpleGraph α) (u : α) :
    ∃ S : Finset α, (∀ x ∈ S, G.Adj u x) ∧ (S : Set α).Pairwise (fun x y => ¬ G.Adj x y) ∧
      S.card = indepNeighborsCard G u := by sorry
