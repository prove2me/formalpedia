-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_app_joint_choice
-- name    : MatchingLogic.IsMCS.app_joint_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:50.971917+00:00
-- url     : https://prove2.me/theorems/12113743-e7ed-4a8c-b75a-5cb4bb551217
-- title:
--   Is MCS: app joint choice
-- statement:
--   Joint finite-product decision used in every stage of the n-ary canonical
--   Existence Lemma.  This includes the nullary case.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalChoice.lean#L148-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalChoice.lean#L148-L161

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}

theorem MatchingLogic.IsMCS.app_joint_choice {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat)
    (psi : Pattern S Nat) (happ : Pattern.app sigma Phi ∈ Gamma) :
    ∃ choose : Fin (S.arity sigma) -> Bool,
      Pattern.app sigma (fun i =>
        Pattern.and (Phi i) (if choose i then psi else Pattern.nt psi)) ∈ Gamma := by sorry
