-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_captureFree_reverse_substVar
-- name    : MatchingLogic.Pattern.captureFree_reverse_substVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:48.6108+00:00
-- url     : https://prove2.me/theorems/4e9ca47b-f9cc-4c71-8d19-3bdebe744b10
-- title:
--   Pattern: capture Free reverse subst Var
-- statement:
--   The reverse leg of a fresh substitution is itself capture-free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L110-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L110-L133

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.captureFree_reverse_substVar {x y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) :
    CaptureFree y x (substVar x y p) := by sorry
