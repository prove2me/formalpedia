-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_freshTuple_not_mem_component_allVars
-- name    : MatchingLogic.Pattern.freshTuple_not_mem_component_allVars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:14.298834+00:00
-- url     : https://prove2.me/theorems/198ce132-75e2-4636-b5b3-464035f49483
-- title:
--   Pattern: fresh Tuple not mem component all Vars
-- statement:
--   The Pattern construction uses the fresh Tuple not mem component all Vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L107-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L107-L115

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

theorem MatchingLogic.Pattern.freshTuple_not_mem_component_allVars (p : Pattern S Nat)
    (Phi : Fin n → Pattern S Nat) (i j : Fin n) : freshTuple p Phi i ∉ (Phi j).allVars := by sorry
