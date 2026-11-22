-- Prove2me | Theorems.Thm_MatchingLogic_mem_canonicalInterp
-- name    : MatchingLogic.mem_canonicalInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:01.268798+00:00
-- url     : https://prove2.me/theorems/1c421136-f31d-44af-a9fb-2737a4eef122
-- title:
--   Matching Logic: mem canonical Interp
-- statement:
--   The Matching Logic construction uses the mem canonical Interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L106-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L106-L113

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCanonicalCore

theorem MatchingLogic.mem_canonicalInterp {sigma : S.Sym}
    {components : Fin (S.arity sigma) → CanonicalCarrier S}
    {Gamma : CanonicalCarrier S} :
    Gamma ∈ canonicalInterp sigma components ↔
      ∀ args : Fin (S.arity sigma) → Pattern S Nat,
        (∀ i, args i ∈ (components i).val) →
          Pattern.app sigma args ∈ Gamma.val := by sorry
