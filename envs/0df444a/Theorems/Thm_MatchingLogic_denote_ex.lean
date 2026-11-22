-- Prove2me | Theorems.Thm_MatchingLogic_denote_ex
-- name    : MatchingLogic.denote_ex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:22.180501+00:00
-- url     : https://prove2.me/theorems/dee04d5c-25c5-4ad7-9574-6fe46c001dcd
-- title:
--   Matching Logic: denote ex
-- statement:
--   The Matching Logic construction uses the denote ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L157-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L157-L158

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

theorem MatchingLogic.denote_ex (ρ : Var → M.carrier) (x : Var) (φ : Pattern S Var) :
    M.denote ρ (.ex x φ) = ⋃ a : M.carrier, M.denote (Function.update ρ x a) φ := by sorry

attribute [defeq] MatchingLogic.denote_ex
