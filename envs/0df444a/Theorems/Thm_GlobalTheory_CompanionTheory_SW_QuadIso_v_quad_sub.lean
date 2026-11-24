-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_v_quad_sub
-- name    : GlobalTheory.CompanionTheory.SW.QuadIso.v_quad_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:47.577732+00:00
-- url     : https://prove2.me/theorems/94798688-45f9-435f-a392-fc412a169039
-- title:
--   Quad Iso: v quad sub
-- statement:
--   The Quad Iso construction uses the v quad sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L86-L89

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

theorem GlobalTheory.CompanionTheory.SW.QuadIso.v_quad_sub {a c t t' : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (ht : Valued.v t < 1) (ht' : Valued.v t' < 1) :
    Valued.v ((a * t + c * t ^ 2) - (a * t' + c * t' ^ 2)) = Valued.v (t - t') := by sorry
