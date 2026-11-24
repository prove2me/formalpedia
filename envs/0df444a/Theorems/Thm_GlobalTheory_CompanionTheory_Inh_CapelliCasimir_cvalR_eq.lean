-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CapelliCasimir_cvalR_eq
-- name    : GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cvalR_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:31:10.756146+00:00
-- url     : https://prove2.me/theorems/5d5dd30e-48ab-47d4-855e-f0208f8c5df6
-- title:
--   Capelli Casimir: cval R eq
-- statement:
--   The Capelli Casimir construction uses the cval R eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/CasOfCapelliVec.lean#L152-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/CasOfCapelliVec.lean#L152-L160

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_CasOfCapelliVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Inh GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Polynomial

theorem GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cvalR_eq {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) :
    ((Formalism.REAL.cvalR ε lam : ℝ) : ℂ)
      = ∑ l, (lam l : ℂ) ^ 2 - ∑ l : Fin n, (((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ)) ^ 2 := by sorry
