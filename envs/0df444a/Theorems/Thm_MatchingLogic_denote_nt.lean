-- Prove2me | Theorems.Thm_MatchingLogic_denote_nt
-- name    : MatchingLogic.denote_nt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:26.728873+00:00
-- url     : https://prove2.me/theorems/67f8e977-4b58-4ac1-a905-010b4af5fa0e
-- title:
--   Matching Logic: denote nt
-- statement:
--   The Matching Logic construction uses the denote nt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L163-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L163-L165

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

theorem MatchingLogic.denote_nt (ρ : Var → M.carrier) (φ : Pattern S Var) :
    M.denote ρ φ.nt = (M.denote ρ φ)ᶜ := by sorry
