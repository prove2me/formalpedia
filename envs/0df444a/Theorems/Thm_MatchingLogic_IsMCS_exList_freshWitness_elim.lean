-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_exList_freshWitness_elim
-- name    : MatchingLogic.IsMCS.exList_freshWitness_elim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:30.744509+00:00
-- url     : https://prove2.me/theorems/79ad79a2-9b44-4df3-a605-fe04bb7b052d
-- title:
--   Is MCS: ex List fresh Witness elim
-- statement:
--   Recursively eliminate an `exList` in a fresh-witness MCS.  The result is
--   an actual raw substitution trace, not an appeal to alpha quotienting.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FreshWitnessElim.lean#L154-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FreshWitnessElim.lean#L154-L178

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}

theorem MatchingLogic.IsMCS.exList_freshWitness_elim {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma)
    (ys : List Nat) (hys : ys.Nodup) (p : Pattern S Nat)
    (hmem : Pattern.exList ys p ∈ Gamma) :
    ∃ zs, Pattern.FreshExListTrace ys zs p ∧ Pattern.substList ys zs p ∈ Gamma := by sorry
