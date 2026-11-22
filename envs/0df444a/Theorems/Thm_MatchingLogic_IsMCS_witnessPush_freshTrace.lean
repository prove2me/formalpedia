-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_witnessPush_freshTrace
-- name    : MatchingLogic.IsMCS.witnessPush_freshTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:07.342071+00:00
-- url     : https://prove2.me/theorems/d5068131-61d4-4abf-b60a-762dfeec7fa9
-- title:
--   Is MCS: witness Push fresh Trace
-- statement:
--   Apply Lemma 80 and eliminate its nested existential witnesses using the
--   fresh strengthened interface.  `FreshExListTrace` records exactly the
--   all-variable freshness available at every recursive step, so consumers do not
--   need to guess a raw-syntax normalization convention.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FreshWitnessElim.lean#L184-L211
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FreshWitnessElim.lean#L184-L211

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

theorem MatchingLogic.IsMCS.witnessPush_freshTrace {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyfreshP : forall i, y i ∉ p.allVars)
    (hyfreshPhi : forall i j, y i ∉ (Phi j).allVars)
    (happ : Pattern.app sigma Phi ∈ Gamma) :
    ∃ z : List Nat,
      Pattern.FreshExListTrace (List.ofFn y) z
        (.app sigma (fun i => Pattern.and (Phi i)
          (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∧
      Pattern.substList (List.ofFn y) z
        (.app sigma (fun i => Pattern.and (Phi i)
          (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∈ Gamma := by sorry
