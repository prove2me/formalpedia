-- Prove2me | Theorems.Thm_MatchingLogic_Provable_and_intro
-- name    : MatchingLogic.Provable.and_intro
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:51.592797+00:00
-- url     : https://prove2.me/theorems/1a84f8e1-2602-42cb-867c-2bfe9b2c03ae
-- title:
--   Provable: and intro
-- statement:
--   Derived conjunction introduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L222-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L222-L229

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.Provable.and_intro {Γ : Set (Pattern S Var)} {φ ψ : Pattern S Var}
    (hφ : Provable Γ φ) (hψ : Provable Γ ψ) :
    Provable Γ (Pattern.and φ ψ) := by sorry
