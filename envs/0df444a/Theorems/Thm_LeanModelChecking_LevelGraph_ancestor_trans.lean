-- Prove2me | Theorems.Thm_LeanModelChecking_LevelGraph_ancestor_trans
-- name    : LeanModelChecking.LevelGraph.ancestor_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:44:01.660898+00:00
-- url     : https://prove2.me/theorems/43e527b1-6aee-4ded-9659-ec84d476a422
-- title:
--   Level Graph: ancestor trans
-- statement:
--   The Level Graph construction uses the ancestor trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L141-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L141-L152

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

theorem LeanModelChecking.LevelGraph.ancestor_trans {i j k} (hij : i ≤ j) (hjk : j ≤ k) (v : G.level k) :
    ancestor hij (ancestor hjk v) = ancestor (hij.trans hjk) v := by sorry
