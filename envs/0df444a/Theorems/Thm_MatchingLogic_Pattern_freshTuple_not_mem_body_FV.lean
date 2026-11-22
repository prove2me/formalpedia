-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_freshTuple_not_mem_body_FV
-- name    : MatchingLogic.Pattern.freshTuple_not_mem_body_FV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:19.813973+00:00
-- url     : https://prove2.me/theorems/d36507bd-03f9-4e10-a1bf-b1fe3404a888
-- title:
--   Pattern: fresh Tuple not mem body FV
-- statement:
--   The Pattern construction uses the fresh Tuple not mem body FV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L117-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L117-L120

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

theorem MatchingLogic.Pattern.freshTuple_not_mem_body_FV (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat)
    (i : Fin n) : freshTuple p Phi i ∉ FV p := by sorry
