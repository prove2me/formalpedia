-- Prove2me | Theorems.Thm_MatchingLogic_denote_defined
-- name    : MatchingLogic.denote_defined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:32.466555+00:00
-- url     : https://prove2.me/theorems/510911f2-4916-482e-940e-9aaf8d9504be
-- title:
--   Matching Logic: denote defined
-- statement:
--   `⌈·⌉` has the semantics of Section 2 in the expansion: `univ` when the
--   argument is inhabited, `∅` when it is empty.  This is a control: if it failed,
--   `expand` would not be interpreting definedness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Definedness.lean#L131-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Definedness.lean#L131-L168

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Definedness
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.denote_defined (M : Model S) (ρ : Var → M.carrier)
    (φ : Pattern (defSig S) Var) :
    ((expand M).denote ρ (defined φ) = Set.univ ↔ ((expand M).denote ρ φ).Nonempty) ∧
      ((expand M).denote ρ (defined φ) = ∅ ↔ (expand M).denote ρ φ = ∅) := by sorry
