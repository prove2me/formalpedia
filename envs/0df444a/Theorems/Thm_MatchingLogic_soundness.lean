-- Prove2me | Theorems.Thm_MatchingLogic_soundness
-- name    : MatchingLogic.soundness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:44.165017+00:00
-- url     : https://prove2.me/theorems/139fa2de-4b1d-4cdb-8310-dc2e927af38f
-- title:
--   Matching Logic: soundness
-- statement:
--   **(S) is provable, not merely assumable.**  The paper cites soundness to its
--   reference [3]; every rule of Figure 2 is sound for global consequence, so it can
--   be discharged here.  Doing so removes one of the two black boxes from
--   Corollary 15.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Soundness.lean#L246-L342
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Soundness.lean#L246-L342

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Sanity
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
attribute [local instance] Classical.propDecidable

theorem MatchingLogic.soundness : Soundness S Var := by sorry
