-- Prove2me | Theorems.Thm_MatchingLogic_canonicalStep_iff
-- name    : MatchingLogic.canonicalStep_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:25.034029+00:00
-- url     : https://prove2.me/theorems/61437dcf-fbb5-4c38-8379-cbd672a293c5
-- title:
--   Matching Logic: canonical Step iff
-- statement:
--   The Matching Logic construction uses the canonical Step iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L70-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L70-L76

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

theorem MatchingLogic.canonicalStep_iff (parent child : CanonicalCarrier S) :
    canonicalStep parent child ↔
      ∃ (sigma : S.Sym)
        (components : Fin (S.arity sigma) → CanonicalCarrier S)
        (i : Fin (S.arity sigma)),
        parent ∈ canonicalInterp sigma components ∧ child = components i := by sorry
