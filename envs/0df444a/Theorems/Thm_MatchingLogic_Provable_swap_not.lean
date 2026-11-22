-- Prove2me | Theorems.Thm_MatchingLogic_Provable_swap_not
-- name    : MatchingLogic.Provable.swap_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:53.428797+00:00
-- url     : https://prove2.me/theorems/0cb7374b-8c9e-410d-abb3-f02e0b1f880b
-- title:
--   Provable: swap not
-- statement:
--   Propositional contraposition in the shape used by quantifier
--   generalisation below.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L70-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L70-L78

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatWitnessed

theorem MatchingLogic.Provable.swap_not {Gamma : Set (Pattern S Nat)}
    {p q : Pattern S Nat} (h : Provable Gamma (.imp p (Pattern.nt q))) :
    Provable Gamma (.imp q (Pattern.nt p)) := by sorry
