-- Prove2me | Theorems.Thm_MatchingLogic_localCons_compact
-- name    : MatchingLogic.localCons_compact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:32.698847+00:00
-- url     : https://prove2.me/theorems/b33abc08-e9c4-4528-b232-fda9938ff112
-- title:
--   Matching Logic: local Cons compact
-- statement:
--   Public form of semantic local compactness, used to reduce arbitrary
--   signatures to the finite symbol support of finitely many premises and the
--   conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L425-L430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L425-L430

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.localCons_compact {Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (hlocal : LocalCons Delta phi) :
    ∃ l : List (Pattern S Var),
      (∀ delta ∈ l, delta ∈ Delta) ∧
        LocalCons {delta | delta ∈ l} phi := by sorry
