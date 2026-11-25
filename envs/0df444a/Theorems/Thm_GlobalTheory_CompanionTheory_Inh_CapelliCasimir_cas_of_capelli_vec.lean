-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CapelliCasimir_cas_of_capelli_vec
-- name    : GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_of_capelli_vec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:57.675864+00:00
-- url     : https://prove2.me/theorems/97c8bf1d-893c-5b4b-bd84-fd169364d94d
-- title:
--   Capelli Casimir: cas of capelli vec
-- statement:
--   The Capelli Casimir construction uses the cas of capelli vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/CasOfCapelliVec.lean#L164-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/CasOfCapelliVec.lean#L164-L221

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
open Formalism.REAL

theorem GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_of_capelli_vec : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (v : V), GlRel E → (∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v) → Cas E v = ((cvalR ε lam : ℝ) : ℂ) • v := by sorry
