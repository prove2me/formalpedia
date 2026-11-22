-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_freshTuple_not_mem_body_allVars
-- name    : MatchingLogic.Pattern.freshTuple_not_mem_body_allVars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:05.303966+00:00
-- url     : https://prove2.me/theorems/b7e7a85d-b675-4d09-b51a-1adb7217daf6
-- title:
--   Pattern: fresh Tuple not mem body all Vars
-- statement:
--   The Pattern construction uses the fresh Tuple not mem body all Vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L99-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L99-L105

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

theorem MatchingLogic.Pattern.freshTuple_not_mem_body_allVars (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat)
    (i : Fin n) : freshTuple p Phi i ∉ p.allVars := by sorry
