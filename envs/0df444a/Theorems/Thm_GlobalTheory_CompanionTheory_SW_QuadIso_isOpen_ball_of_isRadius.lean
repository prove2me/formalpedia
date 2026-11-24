-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_isOpen_ball_of_isRadius
-- name    : GlobalTheory.CompanionTheory.SW.QuadIso.isOpen_ball_of_isRadius
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:49:35.399578+00:00
-- url     : https://prove2.me/theorems/1b49ea60-f984-477a-b965-3bb4dc1c9745
-- title:
--   Quad Iso: is Open ball of is Radius
-- statement:
--   The Quad Iso construction uses the is Open ball of is Radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L35-L38

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

theorem GlobalTheory.CompanionTheory.SW.QuadIso.isOpen_ball_of_isRadius {γ : ℤᵐ⁰} (h : IsRadius K γ) : IsOpen {y : K | Valued.v y < γ} := by sorry
