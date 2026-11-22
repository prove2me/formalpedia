-- Prove2me | Theorems.Thm_MatchingLogic_PForm_subst_rename
-- name    : MatchingLogic.PForm.subst_rename
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:27.287541+00:00
-- url     : https://prove2.me/theorems/93ea97f3-ace4-4de7-8bfa-879ef3824b5a
-- title:
--   PForm: subst rename
-- statement:
--   Renaming commutes with propositional substitution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L163-L169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L163-L169

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.PForm.subst_rename (f : Var → Var') (p : PForm)
    (theta : Nat → Pattern S Var) :
    (p.subst theta).rename f = p.subst (fun n => (theta n).rename f) := by sorry
