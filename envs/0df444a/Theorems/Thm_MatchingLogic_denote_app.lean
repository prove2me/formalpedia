-- Prove2me | Theorems.Thm_MatchingLogic_denote_app
-- name    : MatchingLogic.denote_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:15.507002+00:00
-- url     : https://prove2.me/theorems/31c86a49-15c3-4973-be03-c34bcca10698
-- title:
--   Matching Logic: denote app
-- statement:
--   The Matching Logic construction uses the denote app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L150-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L150-L152

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

theorem MatchingLogic.denote_app (ρ : Var → M.carrier) (σ : S.Sym)
    (f : Fin (S.arity σ) → Pattern S Var) :
    M.denote ρ (.app σ f) = M.app σ (fun i => M.denote ρ (f i)) := by sorry

attribute [defeq] MatchingLogic.denote_app
