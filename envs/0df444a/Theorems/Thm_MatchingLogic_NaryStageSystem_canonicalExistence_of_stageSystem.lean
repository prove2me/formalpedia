-- Prove2me | Theorems.Thm_MatchingLogic_NaryStageSystem_canonicalExistence_of_stageSystem
-- name    : MatchingLogic.NaryStageSystem.canonicalExistence_of_stageSystem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:21.331444+00:00
-- url     : https://prove2.me/theorems/f014530d-b0dc-463f-840d-44e1c881708f
-- title:
--   Nary Stage System: canonical Existence of stage System
-- statement:
--   Once the paper's simultaneous finite-stage invariant has been built, its
--   limit gives exactly the component worlds required by Theorem 73.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L258-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L258-L269

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
open MatchingLogic.NaryStageSystem
variable {sigma : S.Sym} {Gamma : CanonicalCarrier S}
  {phi : Fin (S.arity sigma) → Pattern S Nat} {enum : Nat → Pattern S Nat}
  (T : NaryStageSystem sigma Gamma phi enum)

theorem MatchingLogic.NaryStageSystem.canonicalExistence_of_stageSystem
    (T : NaryStageSystem sigma Gamma phi enum) (henum : Function.Surjective enum) :
    ∃ components : Fin (S.arity sigma) → CanonicalCarrier S,
      (∀ i, phi i ∈ (components i).val) ∧
        Gamma ∈ canonicalInterp sigma components := by sorry
