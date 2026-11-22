-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_freshTuple_not_mem_component_FV
-- name    : MatchingLogic.Pattern.freshTuple_not_mem_component_FV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:19.752207+00:00
-- url     : https://prove2.me/theorems/bef019e0-8209-4804-8df2-07f6e29b40e1
-- title:
--   Pattern: fresh Tuple not mem component FV
-- statement:
--   The Pattern construction uses the fresh Tuple not mem component FV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L122-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L122-L125

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.freshTuple_not_mem_component_FV (p : Pattern S Nat)
    (Phi : Fin n → Pattern S Nat) (i j : Fin n) : freshTuple p Phi i ∉ FV (Phi j) := by sorry
