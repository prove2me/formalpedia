-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_isPiSystem_vball
-- name    : GlobalTheory.CompanionTheory.SW.QuadIso.isPiSystem_vball
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:50:37.457915+00:00
-- url     : https://prove2.me/theorems/dbc7d484-df9d-47b2-b995-828d0ebfefb1
-- title:
--   Quad Iso: is Pi System vball
-- statement:
--   The Quad Iso construction uses the is Pi System vball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L57-L66

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]

theorem GlobalTheory.CompanionTheory.SW.QuadIso.isPiSystem_vball :
    IsPiSystem {s : Set K | ∃ (x : K) (γ : ℤᵐ⁰), s = vball x γ ∧ IsRadius K γ} := by sorry
