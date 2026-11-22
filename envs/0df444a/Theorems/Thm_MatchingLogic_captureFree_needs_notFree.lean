-- Prove2me | Theorems.Thm_MatchingLogic_captureFree_needs_notFree
-- name    : MatchingLogic.captureFree_needs_notFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:08.07981+00:00
-- url     : https://prove2.me/theorems/304580cc-31ef-4d18-88d2-17b235296529
-- title:
--   Matching Logic: capture Free needs not Free
-- statement:
--   **The `x ∉ FV a` alternative is not vacuous.**  Substituting `y` for `x` in
--   `∃y. z`, where `x` does not occur, is harmless — `substVar` leaves the pattern
--   alone — yet the binder is `y` itself. Only the middle alternative admits it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L122-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L122-L127

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.captureFree_needs_notFree :
    CaptureFree (S := S) (Var := Nat) 0 1 (.ex 1 (.var 2)) ∧
      substVar (S := S) (Var := Nat) 0 1 (.ex 1 (.var 2)) = .ex 1 (.var 2) := by sorry
