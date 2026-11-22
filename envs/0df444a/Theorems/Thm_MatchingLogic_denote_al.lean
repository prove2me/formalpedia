-- Prove2me | Theorems.Thm_MatchingLogic_denote_al
-- name    : MatchingLogic.denote_al
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:22.714338+00:00
-- url     : https://prove2.me/theorems/f54e510a-5eb2-4038-a3e6-2b05d818fdb0
-- title:
--   Matching Logic: denote al
-- statement:
--   The Matching Logic construction uses the denote al property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L171-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean#L171-L173

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

theorem MatchingLogic.denote_al (ρ : Var → M.carrier) (x : Var) (φ : Pattern S Var) :
    M.denote ρ (Pattern.al x φ) = ⋂ a : M.carrier, M.denote (Function.update ρ x a) φ := by sorry
