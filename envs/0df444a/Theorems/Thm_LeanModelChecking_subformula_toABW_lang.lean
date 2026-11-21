-- Prove2me | Theorems.Thm_LeanModelChecking_subformula_toABW_lang
-- name    : LeanModelChecking.subformula_toABW_lang
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:22.649073+00:00
-- url     : https://prove2.me/theorems/53093a2c-5172-42a1-bf16-f4b70d378897
-- title:
--   Lean Model Checking: subformula to ABW lang
-- statement:
--   The Lean Model Checking construction uses the subformula to ABW lang property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1157-L1184
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1157-L1184

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

theorem LeanModelChecking.subformula_toABW_lang
  {S} {Φ φ : NNF S} (leφ : φ ≤ Φ)
  {w : ℕ → Letter S}
  {G : RunDAG Φ.toABW w} (G_acc : G.accepting)
  {k : ℕ} {q : Iic Φ} {Y : Set (Iic Φ)}
  (p_sat : PositiveBool.Sat Y (Φ.toABW.δ ⟨φ, leφ⟩ (w k)))
  (p_sub : {(q, k)} ×ˢ Y ⊆ G.E)
    : φ.toABW.language (fun j => w (j + k)) := by sorry
