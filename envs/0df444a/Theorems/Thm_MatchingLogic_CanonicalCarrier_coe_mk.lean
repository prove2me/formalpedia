-- Prove2me | Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
-- name    : MatchingLogic.CanonicalCarrier.coe_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:56.60432+00:00
-- url     : https://prove2.me/theorems/78a9c12e-1cbb-4680-8b50-128f52d1bd28
-- title:
--   Canonical Carrier: coe mk
-- statement:
--   The Canonical Carrier construction uses the coe mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L49-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L49-L52

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
open MatchingLogic.CanonicalCarrier

theorem MatchingLogic.CanonicalCarrier.coe_mk (Gamma : Set (Pattern S Nat))
    (h : IsMCS Gamma ∧ FreshWitnessed Gamma) :
    ((⟨Gamma, h⟩ : CanonicalCarrier S) : Set (Pattern S Nat)) = Gamma := by sorry

attribute [defeq] MatchingLogic.CanonicalCarrier.coe_mk
