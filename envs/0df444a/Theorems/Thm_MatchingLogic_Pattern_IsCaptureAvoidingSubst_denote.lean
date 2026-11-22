-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_denote
-- name    : MatchingLogic.Pattern.IsCaptureAvoidingSubst.denote
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:53.135242+00:00
-- url     : https://prove2.me/theorems/cb384127-8789-4327-8323-571abf370fce
-- title:
--   Is Capture Avoiding Subst: denote
-- statement:
--   The Is Capture Avoiding Subst construction uses the denote property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L401-L407
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L401-L407

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.IsCaptureAvoidingSubst.denote {x y : Nat} {p q : Pattern S Nat}
    (h : IsCaptureAvoidingSubst x y p q) (M : Model S)
    (rho : Nat → M.carrier) :
    M.denote rho q = M.denote (Function.update rho x (rho y)) p := by sorry
