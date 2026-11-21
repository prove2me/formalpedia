-- Prove2me | Theorems.Thm_LeanModelChecking_LevelGraph_ancestor_1
-- name    : LeanModelChecking.LevelGraph.ancestor_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:43:56.034193+00:00
-- url     : https://prove2.me/theorems/39cdaa1d-3495-42a8-b9d7-ce1a0b14b4d8
-- title:
--   Level Graph: ancestor 1
-- statement:
--   The Level Graph construction uses the ancestor 1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L134-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L134-L139

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW
set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.LevelGraph
variable {G : LevelGraph}

theorem LeanModelChecking.LevelGraph.ancestor_1 {i j} (hij : i ≤ j) (v : G.level (j + 1)) :
    ancestor hij (G.ex_parent j v).choose = ancestor (show i ≤ j + 1 by omega) v := by sorry
