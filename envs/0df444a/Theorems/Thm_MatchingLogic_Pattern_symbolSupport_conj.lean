-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_symbolSupport_conj
-- name    : MatchingLogic.Pattern.symbolSupport_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:10.544963+00:00
-- url     : https://prove2.me/theorems/04feb816-f2c0-4dc8-a2ff-ac43c108cc01
-- title:
--   Pattern: symbol Support conj
-- statement:
--   The support of a finite conjunction is the union of the supports of its members.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SymbolSupport.lean#L49-L57
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SymbolSupport.lean#L49-L57

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

theorem MatchingLogic.Pattern.symbolSupport_conj [DecidableEq S.Sym]
    (l : List (Pattern S Var)) :
    (conj l).symbolSupport =
      l.foldr (fun p support => p.symbolSupport ∪ support) ∅ := by sorry
