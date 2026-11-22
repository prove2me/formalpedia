-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_app_alphaEq_mem_iff
-- name    : MatchingLogic.IsMCS.app_alphaEq_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:34.391469+00:00
-- url     : https://prove2.me/theorems/98006f5a-9291-4324-a3b5-178aed70fe52
-- title:
--   Is MCS: app alpha Eq mem iff
-- statement:
--   Pointwise alpha-congruent application arguments have identical MCS
--   membership.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L90-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L90-L94

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.IsMCS

theorem MatchingLogic.IsMCS.app_alphaEq_mem_iff {Gamma : Set (Pattern S Nat)} {sigma : S.Sym}
    {args args' : Fin (S.arity sigma) → Pattern S Nat} (hM : IsMCS Gamma)
    (h : ∀ i, Pattern.AlphaEq (args i) (args' i)) :
    Pattern.app sigma args ∈ Gamma ↔ Pattern.app sigma args' ∈ Gamma := by sorry
