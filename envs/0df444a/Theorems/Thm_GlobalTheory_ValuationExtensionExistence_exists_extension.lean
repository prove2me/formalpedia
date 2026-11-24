-- Prove2me | Theorems.Thm_GlobalTheory_ValuationExtensionExistence_exists_extension
-- name    : GlobalTheory.ValuationExtensionExistence.exists_extension
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:50:24.596719+00:00
-- url     : https://prove2.me/theorems/0f8ee837-d4bc-47cf-81dd-09a1736825d1
-- title:
--   Valuation Extension Existence: exists extension
-- statement:
--   The Valuation Extension Existence construction uses the exists extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherLast.lean#L5-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherLast.lean#L5-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuationExtensionExistence

theorem GlobalTheory.ValuationExtensionExistence.exists_extension {V R K : Type} [CommRing V] [CommRing R] [IsDomain R] [Field K]
    [IsAlgClosed K] [Algebra V R] [Algebra.IsIntegral V R] [FaithfulSMul V R] (ev : V →+* K) :
    ∃ ev₁ : R →+* K, ev₁.comp (algebraMap V R) = ev := by sorry
