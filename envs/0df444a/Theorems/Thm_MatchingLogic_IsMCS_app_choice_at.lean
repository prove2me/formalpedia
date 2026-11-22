-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_app_choice_at
-- name    : MatchingLogic.IsMCS.app_choice_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:39.894288+00:00
-- url     : https://prove2.me/theorems/cb3c9e64-56cb-407e-a25a-d6fb5263e82b
-- title:
--   Is MCS: app choice at
-- statement:
--   The one-coordinate distribution step.  It is the binary branching node in
--   the source's `2^n` disjunction argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalChoice.lean#L76-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalChoice.lean#L76-L105

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}

theorem MatchingLogic.IsMCS.app_choice_at {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (args : Fin (S.arity sigma) -> Pattern S Nat)
    (i : Fin (S.arity sigma)) (psi : Pattern S Nat)
    (happ : Pattern.app sigma args ∈ Gamma) :
    ∃ b : Bool,
      Pattern.app sigma
        (Function.update args i
          (Pattern.and (args i) (if b then psi else Pattern.nt psi))) ∈ Gamma := by sorry
