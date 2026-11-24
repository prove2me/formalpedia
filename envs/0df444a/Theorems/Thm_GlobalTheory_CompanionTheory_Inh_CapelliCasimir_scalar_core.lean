-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CapelliCasimir_scalar_core
-- name    : GlobalTheory.CompanionTheory.Inh.CapelliCasimir.scalar_core
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:21.177429+00:00
-- url     : https://prove2.me/theorems/e8ac83f1-407e-41e7-8282-9e4949ae6746
-- title:
--   Capelli Casimir: scalar core
-- statement:
--   The Capelli Casimir construction uses the scalar core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/CasOfCapelliVec.lean#L41-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/CasOfCapelliVec.lean#L41-L104

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

theorem GlobalTheory.CompanionTheory.Inh.CapelliCasimir.scalar_core (n : ℕ) (hn : 2 ≤ n) (ρ μ a : Fin n → ℂ) (b : Fin n → Fin n → ℂ) (r : ℕ → ℂ)
    (e c : ℂ)
    (h : ∀ Y : ℂ, (∏ l, (Y + ρ l)) * e + ∑ i, (∏ l ∈ univ.erase i, (Y + ρ l)) * a i
      + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (∏ l ∈ (univ.erase i).erase j, (Y + ρ l)) * b i j
      + ∑ d ∈ range (n - 2), (Y + c) ^ d * r d = (∏ l, (Y + μ l)) * e) :
    (∑ l, ρ l) * e + ∑ i, a i = (∑ l, μ l) * e ∧
    ((∑ l, ρ l) ^ 2 - ∑ l, ρ l ^ 2) * e + 2 * ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i
      + 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), b i j
      = ((∑ l, μ l) ^ 2 - ∑ l, μ l ^ 2) * e := by sorry
