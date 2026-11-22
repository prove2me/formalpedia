-- Prove2me | Theorems.Thm_MatchingLogic_denote_bot
-- name    : MatchingLogic.denote_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:17.006994+00:00
-- url     : https://prove2.me/theorems/218967cb-e326-44ee-a204-d4947294537b
-- title:
--   Matching Logic: denote bot
-- statement:
--   The Matching Logic construction uses the denote bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L147-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L147-L148

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
variable {S : Signature} {Var : Type} [DecidableEq Var] (M : Model S)

theorem MatchingLogic.denote_bot (ρ : Var → M.carrier) :
    M.denote ρ (.bot : Pattern S Var) = ∅ := by sorry

attribute [defeq] MatchingLogic.denote_bot
