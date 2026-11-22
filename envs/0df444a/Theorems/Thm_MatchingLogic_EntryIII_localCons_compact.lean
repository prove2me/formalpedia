-- Prove2me | Theorems.Thm_MatchingLogic_EntryIII_localCons_compact
-- name    : MatchingLogic.EntryIII.localCons_compact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:49.097828+00:00
-- url     : https://prove2.me/theorems/317f918a-4292-40ea-95b4-1f814e669957
-- title:
--   Entry III: local Cons compact
-- statement:
--   **Semantic local compactness for matching logic.**  No countability
--   assumption is needed on the matching-symbol type or on the variable type.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L339-L414
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L339-L414

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIII
open FirstOrder
universe u
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.EntryIII.localCons_compact {Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (hlocal : LocalCons Delta phi) :
    ∃ l : List (Pattern S Var),
      (∀ delta ∈ l, delta ∈ Delta) ∧
        LocalCons {delta | delta ∈ l} phi := by sorry
