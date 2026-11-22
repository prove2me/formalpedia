-- Prove2me | Theorems.Thm_MatchingLogic_denote_var
-- name    : MatchingLogic.denote_var
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:14.509868+00:00
-- url     : https://prove2.me/theorems/f99f3774-ed64-4b77-bda5-2de7e2bf53d8
-- title:
--   Matching Logic: denote var
-- statement:
--   The Matching Logic construction uses the denote var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L144-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L144-L145

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

theorem MatchingLogic.denote_var (ρ : Var → M.carrier) (x : Var) :
    M.denote ρ (.var x) = {ρ x} := by sorry

attribute [defeq] MatchingLogic.denote_var
