-- Prove2me | Theorems.Thm_MatchingLogic_LocProvable_not_ex_of_not_fresh
-- name    : MatchingLogic.LocProvable.not_ex_of_not_fresh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:55.657069+00:00
-- url     : https://prove2.me/theorems/ac477575-1760-4c32-99e0-59b4f4b66949
-- title:
--   Loc Provable: not ex of not fresh
-- statement:
--   Local universal generalisation of a negation.  The side condition is the
--   source condition that the generalised name is absent from every premise.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L119-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L119-L133

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

theorem MatchingLogic.LocProvable.not_ex_of_not_fresh {Gamma : Set (Pattern S Nat)}
    {y : Nat} {q : Pattern S Nat}
    (hfresh : ∀ p ∈ Gamma, y ∉ FV p)
    (hnot : LocProvable Gamma (Pattern.nt q)) :
    LocProvable Gamma (Pattern.nt (.ex y q)) := by sorry
