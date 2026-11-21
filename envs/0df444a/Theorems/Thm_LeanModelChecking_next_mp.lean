-- Prove2me | Theorems.Thm_LeanModelChecking_next_mp
-- name    : LeanModelChecking.next_mp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:46:42.604558+00:00
-- url     : https://prove2.me/theorems/adc58686-40b3-4970-8d54-9ce196bbb01d
-- title:
--   Lean Model Checking: next mp
-- statement:
--   The Lean Model Checking construction uses the next mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1282-L1294
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1282-L1294

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking

theorem LeanModelChecking.next_mp {AP : Type} {φ : NNF AP} {w} : φ.next.toABW.language w
    → φ.toABW.language (fun j => w (j + 1)) := by sorry
