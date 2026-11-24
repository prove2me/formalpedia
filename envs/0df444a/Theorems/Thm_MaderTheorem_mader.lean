-- Prove2me | Theorems.Thm_MaderTheorem_mader
-- name    : MaderTheorem.mader
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:59:21.866919+00:00
-- url     : https://prove2.me/theorems/e11436a3-6d2f-47d2-b4fe-99e366593454
-- title:
--   Mader Theorem: mader
-- statement:
--   **Mader (1972)**, in the form of Diestel's Theorem 1.4.3.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/Solution.lean#L36-L41
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/Solution.lean#L36-L41

module
public import Mathlib
public import Definitions.Def_MaderLib_Mader
public import Definitions.Def_MaderLib_Solution
public import Theorems.Thm_Mader_mader

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open MaderTheorem
variable {V : Type*}

theorem MaderTheorem.mader [Fintype V] [Nonempty V] (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hd : 4 * k * Fintype.card V ≤ 2 * G.edgeSet.ncard) :
    ∃ S : Finset V, IsKConnected (G.induce (S : Set V)) (k + 1) ∧
      (G.edgeSet.ncard : ℝ) / Fintype.card V - k <
        ((G.induce (S : Set V)).edgeSet.ncard : ℝ) / S.card := by sorry
