-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_exList_witness_elim
-- name    : MatchingLogic.IsMCS.exList_witness_elim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:32.662328+00:00
-- url     : https://prove2.me/theorems/3904e68f-4098-4769-88b6-939c252c7e0b
-- title:
--   Is MCS: ex List witness elim
-- statement:
--   Eliminate the nested witnesses produced by Lemma 80 and normalize every
--   sequential raw substitution back to one source-style substitution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessElim.lean#L460-L488
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessElim.lean#L460-L488

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessElim
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}

theorem MatchingLogic.IsMCS.exList_witness_elim {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyfreshP : forall i, y i ∉ p.allVars)
    (hyfreshPhi : forall i j, y i ∉ (Phi j).allVars)
    (hnested : Pattern.exList (List.ofFn y)
      (.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∈ Gamma) :
    ∃ z : Fin (S.arity sigma) -> Nat,
      (forall i, z i ∉ p.allVars) ∧
      (forall i j, z i ∉ (Phi j).allVars) ∧
      Pattern.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (z i) p))) ∈ Gamma := by sorry
