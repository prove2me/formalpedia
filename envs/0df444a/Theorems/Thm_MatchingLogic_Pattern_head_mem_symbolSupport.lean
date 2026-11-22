-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_head_mem_symbolSupport
-- name    : MatchingLogic.Pattern.head_mem_symbolSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:01.510724+00:00
-- url     : https://prove2.me/theorems/f9a04b81-e7c1-40ab-bfaa-d8d49a27ac97
-- title:
--   Pattern: head mem symbol Support
-- statement:
--   Every head symbol belongs to the support of its application pattern.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SymbolSupport.lean#L35-L38
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SymbolSupport.lean#L35-L38

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

theorem MatchingLogic.Pattern.head_mem_symbolSupport [DecidableEq S.Sym]
    (sigma : S.Sym) (args : Fin (S.arity sigma) → Pattern S Var) :
    sigma ∈ (Pattern.app sigma args).symbolSupport := by sorry
