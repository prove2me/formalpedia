-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_captureFree_of_not_mem_allVars
-- name    : MatchingLogic.Pattern.captureFree_of_not_mem_allVars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:55.000876+00:00
-- url     : https://prove2.me/theorems/e11c7f56-8cf8-4aa1-a013-a2a922958c17
-- title:
--   Pattern: capture Free of not mem all Vars
-- statement:
--   A name absent from all raw occurrences is capture-free as a replacement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L90-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L90-L107

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

theorem MatchingLogic.Pattern.captureFree_of_not_mem_allVars {x y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) : CaptureFree x y p := by sorry
