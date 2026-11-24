-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_exists_near
-- name    : GlobalTheory.CompanionTheory.SW.QuadIso.exists_near
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:50:19.819067+00:00
-- url     : https://prove2.me/theorems/db3fed9e-2415-4d21-801a-7e8f10c53bf0
-- title:
--   Quad Iso: exists near
-- statement:
--   The Quad Iso construction uses the exists near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L132-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L132-L141

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

theorem GlobalTheory.CompanionTheory.SW.QuadIso.exists_near {a c x : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (hx : Valued.v x < 1) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    ∃ t : K, Valued.v t < 1 ∧ Valued.v ((a * t + c * t ^ 2) - x) < γ := by sorry
