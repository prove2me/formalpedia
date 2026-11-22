-- Prove2me | Theorems.Thm_MatchingLogic_NaryStageSystem_limit_witnessed
-- name    : MatchingLogic.NaryStageSystem.limit_witnessed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:22.029805+00:00
-- url     : https://prove2.me/theorems/eecee99e-bb67-423d-aa69-962cfcb9f983
-- title:
--   Nary Stage System: limit witnessed
-- statement:
--   The Nary Stage System construction uses the limit witnessed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L214-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L214-L216

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

theorem MatchingLogic.NaryStageSystem.limit_witnessed (henum : Function.Surjective enum)
    (i : Fin (S.arity sigma)) : Witnessed (T.limit i) := by sorry
