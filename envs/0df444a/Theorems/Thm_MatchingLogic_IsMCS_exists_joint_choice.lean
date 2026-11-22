-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_exists_joint_choice
-- name    : MatchingLogic.IsMCS.exists_joint_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:51.917575+00:00
-- url     : https://prove2.me/theorems/e6bf675e-3f13-4f03-98f7-67400c1748af
-- title:
--   Is MCS: exists joint choice
-- statement:
--   List-conjunction specialization consumed directly by the simultaneous
--   finite-stage construction in the canonical Existence Lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalChoice.lean#L165-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalChoice.lean#L165-L173

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}

theorem MatchingLogic.IsMCS.exists_joint_choice {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (L : Fin (S.arity sigma) -> List (Pattern S Nat))
    (psi : Pattern S Nat)
    (happ : Pattern.app sigma (fun i => conj (L i)) ∈ Gamma) :
    ∃ choose : Fin (S.arity sigma) -> Bool,
      Pattern.app sigma (fun i => Pattern.and (conj (L i))
        (if choose i then psi else Pattern.nt psi)) ∈ Gamma := by sorry
