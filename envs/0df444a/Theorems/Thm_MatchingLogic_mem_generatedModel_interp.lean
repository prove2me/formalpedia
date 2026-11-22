-- Prove2me | Theorems.Thm_MatchingLogic_mem_generatedModel_interp
-- name    : MatchingLogic.mem_generatedModel_interp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:26.374704+00:00
-- url     : https://prove2.me/theorems/bf64e1cc-946f-4dbe-9526-6cce197f9d0e
-- title:
--   Matching Logic: mem generated Model interp
-- statement:
--   The Matching Logic construction uses the mem generated Model interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L131-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L131-L136

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

theorem MatchingLogic.mem_generatedModel_interp {root : CanonicalCarrier S}
    {sigma : S.Sym} {components : Fin (S.arity sigma) → GeneratedCarrier root}
    {world : GeneratedCarrier root} :
    world ∈ (generatedModel root).interp sigma components ↔
      world.val ∈ canonicalInterp sigma (fun i => (components i).val) := by sorry
