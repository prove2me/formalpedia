-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_canonical_constructions_are_inhabited
-- name    : MatchingLogic.EntryIIIRegression.canonical_constructions_are_inhabited
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:13.946722+00:00
-- url     : https://prove2.me/theorems/b19a9f89-28ee-4d22-bf10-643cd81f8187
-- title:
--   Entry IIIRegression: canonical constructions are inhabited
-- statement:
--   Canonical, generated, and completed model carriers all expose real points.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L330-L342
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L330-L342

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalConstruction
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Regression
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIIIRegression
open Set
attribute [local instance] MatchingLogic.EntryIIIRegression.instEncodableAuditSym
attribute [local instance] MatchingLogic.EntryIIIRegression.auditPatternCountable

theorem MatchingLogic.EntryIIIRegression.canonical_constructions_are_inhabited :
    ∃ root : CanonicalCarrier AuditSig,
      Nonempty (canonicalModel root).carrier ∧
      Nonempty (generatedModel root).carrier ∧
      Nonempty (completedModel root).carrier ∧
      completedEmbed root (generatedRoot root) ∈ Set.univ := by sorry
