-- Prove2me | Theorems.Thm_MatchingLogic_mem_canonicalModel_interp
-- name    : MatchingLogic.mem_canonicalModel_interp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:45.284798+00:00
-- url     : https://prove2.me/theorems/e86c89e8-d65d-4af0-b254-e588f4fde9e4
-- title:
--   Matching Logic: mem canonical Model interp
-- statement:
--   The Matching Logic construction uses the mem canonical Model interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L120-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L120-L127

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

theorem MatchingLogic.mem_canonicalModel_interp (root : CanonicalCarrier S)
    {sigma : S.Sym} {components : Fin (S.arity sigma) → CanonicalCarrier S}
    {Gamma : CanonicalCarrier S} :
    Gamma ∈ (canonicalModel root).interp sigma components ↔
      ∀ args : Fin (S.arity sigma) → Pattern S Nat,
        (∀ i, args i ∈ (components i).val) →
          Pattern.app sigma args ∈ Gamma.val := by sorry
