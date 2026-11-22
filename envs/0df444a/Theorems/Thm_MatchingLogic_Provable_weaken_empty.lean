-- Prove2me | Theorems.Thm_MatchingLogic_Provable_weaken_empty
-- name    : MatchingLogic.Provable.weaken_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:55.295133+00:00
-- url     : https://prove2.me/theorems/5c322333-1593-4688-8cee-3023c20beb4c
-- title:
--   Provable: weaken empty
-- statement:
--   A theorem is usable under arbitrary hypotheses.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L202-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L202-L204

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.Provable.weaken_empty {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (h : Provable (∅ : Set (Pattern S Var)) φ) : Provable Γ φ := by sorry
