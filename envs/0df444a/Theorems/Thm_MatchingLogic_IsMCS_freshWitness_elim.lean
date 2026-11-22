-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_freshWitness_elim
-- name    : MatchingLogic.IsMCS.freshWitness_elim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:25.237409+00:00
-- url     : https://prove2.me/theorems/0c170a2a-9751-42a7-921b-5530aa52309c
-- title:
--   Is MCS: fresh Witness elim
-- statement:
--   One fresh witness may be eliminated inside an MCS while retaining the
--   strong raw freshness fact needed by subsequent substitutions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FreshWitnessElim.lean#L128-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FreshWitnessElim.lean#L128-L133

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

theorem MatchingLogic.IsMCS.freshWitness_elim {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {y : Nat} {q : Pattern S Nat}
    (hmem : Pattern.ex y q ∈ Gamma) :
    ∃ z, z ∉ q.allVars ∧ Pattern.captureAvoidingSubst y z q ∈ Gamma := by sorry
