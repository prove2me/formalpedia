-- Prove2me | Theorems.Thm_MatchingLogic_mem_generatedInterp
-- name    : MatchingLogic.mem_generatedInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:13.757854+00:00
-- url     : https://prove2.me/theorems/a881ef3e-a041-4faa-bc30-b515537abaf4
-- title:
--   Matching Logic: mem generated Interp
-- statement:
--   The Matching Logic construction uses the mem generated Interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L117-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L117-L122

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated

theorem MatchingLogic.mem_generatedInterp {root : CanonicalCarrier S} {sigma : S.Sym}
    {components : Fin (S.arity sigma) → GeneratedCarrier root}
    {world : GeneratedCarrier root} :
    world ∈ generatedInterp root sigma components ↔
      world.val ∈ canonicalInterp sigma (fun i => (components i).val) := by sorry
