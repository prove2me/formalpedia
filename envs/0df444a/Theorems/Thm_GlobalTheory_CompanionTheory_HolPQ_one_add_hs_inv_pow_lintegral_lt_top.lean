-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolPQ_one_add_hs_inv_pow_lintegral_lt_top
-- name    : GlobalTheory.CompanionTheory.HolPQ.one_add_hs_inv_pow_lintegral_lt_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:47.349181+00:00
-- url     : https://prove2.me/theorems/24f74d80-8439-44ac-9888-c163e37ec5ed
-- title:
--   Hol PQ: one add hs inv pow lintegral lt top
-- statement:
--   The Hol PQ construction uses the one add hs inv pow lintegral lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/OneAddHsInvPowLintegralLtTop.lean#L103-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/OneAddHsInvPowLintegralLtTop.lean#L103-L117

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

theorem GlobalTheory.CompanionTheory.HolPQ.one_add_hs_inv_pow_lintegral_lt_top : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
    ∫⁻ g, ENNReal.ofReal (((1 + hs (umat g))⁻¹) ^ s) ∂(muG ε) < ⊤ := by sorry
