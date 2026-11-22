-- Prove2me | Theorems.Thm_MatchingLogic_localCons_list_iff
-- name    : MatchingLogic.localCons_list_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:48.274965+00:00
-- url     : https://prove2.me/theorems/5a5a75e3-8e14-440f-8446-f738b84bbadd
-- title:
--   Matching Logic: local Cons list iff
-- statement:
--   Pointwise form of local consequence from a finite list.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FiniteReduction.lean#L42-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FiniteReduction.lean#L42-L53

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

theorem MatchingLogic.localCons_list_iff (l : List (Pattern S Var)) (phi : Pattern S Var) :
    LocalCons {delta | delta ∈ l} phi ↔
      ∀ (M : Model S) (rho : Var → M.carrier),
        M.denote rho (conj l) ⊆ M.denote rho phi := by sorry
