-- Prove2me | Theorems.Thm_MatchingLogic_provable_top
-- name    : MatchingLogic.provable_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:39.928402+00:00
-- url     : https://prove2.me/theorems/7480c551-1a37-4942-bffa-c1c52209e2d0
-- title:
--   Matching Logic: provable top
-- statement:
--   `⊤` is derivable in every theory.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L211-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L211-L213

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.provable_top (Γ : Set (Pattern S Var)) :
    Provable Γ (Pattern.tp : Pattern S Var) := by sorry
