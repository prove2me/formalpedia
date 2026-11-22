-- Prove2me | Theorems.Thm_MatchingLogic_denote_imp
-- name    : MatchingLogic.denote_imp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:16.424919+00:00
-- url     : https://prove2.me/theorems/6355a360-ad58-47a2-898b-c4c19dacb7ca
-- title:
--   Matching Logic: denote imp
-- statement:
--   The Matching Logic construction uses the denote imp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L154-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L154-L155

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

theorem MatchingLogic.denote_imp (ρ : Var → M.carrier) (φ ψ : Pattern S Var) :
    M.denote ρ (.imp φ ψ) = (M.denote ρ φ)ᶜ ∪ M.denote ρ ψ := by sorry

attribute [defeq] MatchingLogic.denote_imp
