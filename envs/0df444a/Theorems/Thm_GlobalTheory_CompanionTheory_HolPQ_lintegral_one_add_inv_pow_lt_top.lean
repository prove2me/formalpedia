-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolPQ_lintegral_one_add_inv_pow_lt_top
-- name    : GlobalTheory.CompanionTheory.HolPQ.lintegral_one_add_inv_pow_lt_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:37.013829+00:00
-- url     : https://prove2.me/theorems/4670d622-8826-43ca-931c-7676afa0f869
-- title:
--   Hol PQ: lintegral one add inv pow lt top
-- statement:
--   The Hol PQ construction uses the lintegral one add inv pow lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/OneAddHsInvPowLintegralLtTop.lean#L21-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/OneAddHsInvPowLintegralLtTop.lean#L21-L101

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_OneAddHsInvPowLintegralLtTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset PI.UpqRep
open scoped InnerProductSpace ENNReal ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolPQ

theorem GlobalTheory.CompanionTheory.HolPQ.lintegral_one_add_inv_pow_lt_top {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (h : X → ℝ) (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) (d : ℕ) (C : ℝ)
    (hC : ∀ k : ℕ, μ {x | h x ≤ (4 : ℝ) ^ k} ≤ ENNReal.ofReal (C * ((4 : ℝ) ^ k) ^ d))
    (s : ℕ) (hs' : d + 1 ≤ s) :
    ∫⁻ x, ENNReal.ofReal (((1 + h x)⁻¹) ^ s) ∂μ < ⊤ := by sorry
