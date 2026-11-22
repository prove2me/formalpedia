-- Prove2me | Theorems.Thm_MatchingLogic_Provable_witnessPush
-- name    : MatchingLogic.Provable.witnessPush
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:00.372976+00:00
-- url     : https://prove2.me/theorems/f0fda01a-a236-416a-a959-276133cb5a9c
-- title:
--   Provable: witness Push
-- statement:
--   Technical witness-pushing lemma, Chen--Rosu TR Lemma 80, for every finite
--   arity (including zero).  The hypotheses say that the witnesses are pairwise
--   distinct and do not occur free in `phi` or in any original argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L408-L442
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L408-L442

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}

theorem MatchingLogic.Provable.witnessPush {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (phi : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyphi : forall i, y i ∉ FV phi)
    (hyPhi : forall i j, y i ∉ FV (Phi j)) :
    Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma Phi)
        (Pattern.exList (List.ofFn y)
          (.app sigma (fun i => Pattern.and (Phi i)
            (.imp (.ex x phi)
              (Pattern.captureAvoidingSubst x (y i) phi)))))) := by sorry
