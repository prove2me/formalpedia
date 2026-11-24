-- Prove2me | Theorems.Thm_GlobalTheory_ContinuousValuationExtension_continuous_of_valuation_eq
-- name    : GlobalTheory.ContinuousValuationExtension.continuous_of_valuation_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:25:21.995903+00:00
-- url     : https://prove2.me/theorems/3d12faca-a3ce-46d8-928c-4cacdda218b1
-- title:
--   Continuous Valuation Extension: continuous of valuation eq
-- statement:
--   The Continuous Valuation Extension construction uses the continuous of valuation eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsContinuousExtension.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsContinuousExtension.lean#L7-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsContinuousExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open GlobalTheory GlobalTheory.ContinuousValuationExtension

theorem GlobalTheory.ContinuousValuationExtension.continuous_of_valuation_eq {A B Γ : Type} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ] (g : A →+* B)
    (hs : Function.Surjective (Valued.v : A → Γ))
    (hg : ∀ x : A, (Valued.v (g x) : Γ) = Valued.v x) : Continuous g := by sorry
