-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_witnessPush_elim
-- name    : MatchingLogic.IsMCS.witnessPush_elim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:39.942707+00:00
-- url     : https://prove2.me/theorems/639d1faa-e51a-44a9-b1f4-c633a2241f24
-- title:
--   Is MCS: witness Push elim
-- statement:
--   Stage-recursion interface: apply Lemma 80 and immediately eliminate its
--   nested witnesses inside a witnessed MCS.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessElim.lean#L492-L517
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessElim.lean#L492-L517

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

theorem MatchingLogic.IsMCS.witnessPush_elim {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyfreshP : forall i, y i ∉ p.allVars)
    (hyfreshPhi : forall i j, y i ∉ (Phi j).allVars)
    (happ : Pattern.app sigma Phi ∈ Gamma) :
    ∃ z : Fin (S.arity sigma) -> Nat,
      (forall i, z i ∉ p.allVars) ∧
      (forall i j, z i ∉ (Phi j).allVars) ∧
      Pattern.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (z i) p))) ∈ Gamma := by sorry
