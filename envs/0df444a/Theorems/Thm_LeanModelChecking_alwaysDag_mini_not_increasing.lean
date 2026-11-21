-- Prove2me | Theorems.Thm_LeanModelChecking_alwaysDag_mini_not_increasing
-- name    : LeanModelChecking.alwaysDag.mini_not_increasing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:47.206719+00:00
-- url     : https://prove2.me/theorems/c7cc1935-0758-40b3-930b-40c5b36b2379
-- title:
--   always Dag: mini not increasing
-- statement:
--   The always Dag construction uses the mini not increasing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L867-L878
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L867-L878

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
open LeanModelChecking.alwaysDag
variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (ltφ : φ < Φ)
variable (G : ℕ → DAG (Iic φ))

theorem LeanModelChecking.alwaysDag.mini_not_increasing q l q' (He : ((q.embedLe ltφ.le, l),
    q'.embedLe ltφ.le) ∈ E G) : mini G (q', l + 1) ≤ mini G (q, l) := by sorry
