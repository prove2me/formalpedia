-- Prove2me | Theorems.Thm_MatchingLogic_Provable_and_decide
-- name    : MatchingLogic.Provable.and_decide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:33.396337+00:00
-- url     : https://prove2.me/theorems/072ece66-c2bc-40be-bbe0-9ba72f163d9f
-- title:
--   Provable: and decide
-- statement:
--   Propositional decision while retaining the current finite-stage
--   conjunction: `Phi -> (Phi and psi) or (Phi and not psi)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalChoice.lean#L52-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalChoice.lean#L52-L72

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}

theorem MatchingLogic.Provable.and_decide {Gamma : Set (Pattern S Nat)}
    (Phi psi : Pattern S Nat) :
    Provable Gamma (.imp Phi
      (Pattern.or (Pattern.and Phi psi) (Pattern.and Phi (Pattern.nt psi)))) := by sorry
