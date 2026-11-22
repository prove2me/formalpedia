-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_argument_symbolSupport_subset
-- name    : MatchingLogic.Pattern.argument_symbolSupport_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:10.706016+00:00
-- url     : https://prove2.me/theorems/f9160230-630c-4b74-ae40-a1e8c1668618
-- title:
--   Pattern: argument symbol Support subset
-- statement:
--   Every symbol of an argument belongs to the support of the whole application.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SymbolSupport.lean#L41-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SymbolSupport.lean#L41-L46

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.argument_symbolSupport_subset [DecidableEq S.Sym]
    (sigma : S.Sym) (args : Fin (S.arity sigma) → Pattern S Var) (i : Fin (S.arity sigma)) :
    (args i).symbolSupport ⊆ (Pattern.app sigma args).symbolSupport := by sorry
