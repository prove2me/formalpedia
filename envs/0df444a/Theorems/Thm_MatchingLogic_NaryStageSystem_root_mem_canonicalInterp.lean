-- Prove2me | Theorems.Thm_MatchingLogic_NaryStageSystem_root_mem_canonicalInterp
-- name    : MatchingLogic.NaryStageSystem.root_mem_canonicalInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:01.669309+00:00
-- url     : https://prove2.me/theorems/754db827-e9fc-41aa-be72-6e47888be229
-- title:
--   Nary Stage System: root mem canonical Interp
-- statement:
--   The joint invariant implies the universal membership condition of the
--   canonical interpretation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L239-L254
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L239-L254

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

theorem MatchingLogic.NaryStageSystem.root_mem_canonicalInterp (henum : Function.Surjective enum) :
    Gamma ∈ canonicalInterp sigma
        (fun i => ⟨T.limit i, ⟨T.limit_isMCS henum i,
          T.limit_freshWitnessed henum i⟩⟩) := by sorry
