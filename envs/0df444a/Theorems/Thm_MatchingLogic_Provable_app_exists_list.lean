-- Prove2me | Theorems.Thm_MatchingLogic_Provable_app_exists_list
-- name    : MatchingLogic.Provable.app_exists_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:25.098032+00:00
-- url     : https://prove2.me/theorems/91759d96-aed5-49db-8b9c-6171aeaf4748
-- title:
--   Provable: app exists list
-- statement:
--   Simultaneously pull a finite tuple of existential arguments out of a
--   symbol application.  Pairwise freshness is exactly the side condition of
--   Propagation of Existential.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L386-L403
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L386-L403

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

theorem MatchingLogic.Provable.app_exists_list {Gamma : Set (Pattern S Nat)}
    {sigma : S.Sym} (y : Fin (S.arity sigma) -> Nat)
    (body : Fin (S.arity sigma) -> Pattern S Nat)
    (hfresh : forall i j, i ≠ j -> y i ∉ FV (body j)) :
    Provable Gamma (.imp
      (.app sigma (fun i => .ex (y i) (body i)))
      (Pattern.exList (List.ofFn y) (.app sigma body))) := by sorry
