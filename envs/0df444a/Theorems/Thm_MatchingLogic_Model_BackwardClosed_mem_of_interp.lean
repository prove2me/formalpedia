-- Prove2me | Theorems.Thm_MatchingLogic_Model_BackwardClosed_mem_of_interp
-- name    : MatchingLogic.Model.BackwardClosed.mem_of_interp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:29.755341+00:00
-- url     : https://prove2.me/theorems/268f728a-d6fa-474e-936b-f9ab0cdd89fb
-- title:
--   Backward Closed: mem of interp
-- statement:
--   The concrete form used in the proofs: if a point of `C` is produced by a
--   tuple, every component of that tuple lies in `C` (paper, Definition 2, second
--   sentence).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L197-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L197-L200

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Core
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
universe u
variable (S : Signature) (Var : Type)
attribute [instance] Model.nonempty
open MatchingLogic.Model
variable {S : Signature} (M : Model S)

theorem MatchingLogic.Model.BackwardClosed.mem_of_interp {C : Set M.carrier} (hC : M.BackwardClosed C)
    {σ : S.Sym} {a : Fin (S.arity σ) → M.carrier} {u : M.carrier}
    (hu : u ∈ C) (ha : u ∈ M.interp σ a) (i : Fin (S.arity σ)) : a i ∈ C := by sorry
