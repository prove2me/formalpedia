-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalFieldValuationRing_isFractionRing_integer
-- name    : GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:36.262841+00:00
-- url     : https://prove2.me/theorems/4732cc44-5954-434e-8076-13290a7f241c
-- title:
--   Local Field Valuation Ring: is Fraction Ring integer
-- statement:
--   The Local Field Valuation Ring construction uses the is Fraction Ring integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsFractionRingInteger.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsFractionRingInteger.lean#L5-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsFractionRingInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalFieldValuationRing

theorem GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsFractionRing (ValuativeRel.valuation k).integer k := by sorry
