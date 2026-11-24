-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_nonarchimedeanLocalField_secondCountable_t2Space
-- name    : GlobalTheory.CompanionTheory.QLTop.nonarchimedeanLocalField_secondCountable_t2Space
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:43.533807+00:00
-- url     : https://prove2.me/theorems/57e6732d-d46c-4157-b59c-d04ae46a075a
-- title:
--   QLTop: nonarchimedean Local Field second Countable t2 Space
-- statement:
--   The QLTop construction uses the nonarchimedean Local Field second Countable t2 Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpen.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpen.lean#L13-L23

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLTop
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.CompanionTheory.QLTop.nonarchimedeanLocalField_secondCountable_t2Space (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k ∧ T2Space k := by sorry
