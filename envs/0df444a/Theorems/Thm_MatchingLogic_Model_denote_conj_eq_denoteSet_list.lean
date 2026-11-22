-- Prove2me | Theorems.Thm_MatchingLogic_Model_denote_conj_eq_denoteSet_list
-- name    : MatchingLogic.Model.denote_conj_eq_denoteSet_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:24.629631+00:00
-- url     : https://prove2.me/theorems/cb3fc8a8-052d-45ce-8f41-a9d0db7e04a0
-- title:
--   Model: denote conj eq denote Set list
-- statement:
--   A finite conjunction denotes the same set as the conjunctive denotation of
--   the corresponding list-membership theory.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FiniteReduction.lean#L31-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FiniteReduction.lean#L31-L39

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FiniteReduction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.Model.denote_conj_eq_denoteSet_list (M : Model S)
    (rho : Var → M.carrier) (l : List (Pattern S Var)) :
    M.denote rho (conj l) = M.denoteSet rho {delta | delta ∈ l} := by sorry
