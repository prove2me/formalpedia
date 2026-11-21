-- Prove2me | Theorems.Thm_LeanModelChecking_replaceRoot_runDag_accepting
-- name    : LeanModelChecking.replaceRoot.runDag_accepting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:36.209286+00:00
-- url     : https://prove2.me/theorems/25890912-d4ba-4540-ab84-4a991939466c
-- title:
--   replace Root: run Dag accepting
-- statement:
--   If the source run DAG `G` is accepting and the embedding `embedLe hle` reflects
--   the acceptance condition (`hF`), then the transported `replaceRoot.runDag` is
--   accepting too.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L369-L385
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L369-L385

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
open LeanModelChecking.replaceRoot
variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)

theorem LeanModelChecking.replaceRoot.runDag_accepting
  {S}
  {M : ABW S (Iic φ₁)} {M' : ABW S (Iic φ₂)} {w : ℕ → S}
  {G : RunDAG M w} (G_acc : G.accepting)
  (h_delta_root : ∀ Q, PositiveBool.Sat Q (M.δ M.q₀ (w 0))
      → PositiveBool.Sat ((Subtype.embedLe hle) '' Q) (M'.δ M'.q₀ (w 0)))
  (h_delta_eq : ∀ (q : Iic φ₁) i,
      M'.δ (q.embedLe hle) (w i) = (M.δ q (w i)).mapSubtypeImp (fun _ p => p.trans hle))
  (hF : ∀ q : Iic φ₁, q.embedLe hle ∈ M'.F ↔ q ∈ M.F)
    : (runDag hle G h_delta_root h_delta_eq).accepting := by sorry
