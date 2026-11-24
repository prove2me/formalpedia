-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_measure_ball
-- name    : GlobalTheory.CompanionTheory.SW.QuadIso.measure_ball
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:50:36.308576+00:00
-- url     : https://prove2.me/theorems/dea48f4d-8334-4c5a-8b24-bdee1996a53d
-- title:
--   Quad Iso: measure ball
-- statement:
--   The Quad Iso construction uses the measure ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L145-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L145-L190

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
variable [MeasurableSpace K] [BorelSpace K]

theorem GlobalTheory.CompanionTheory.SW.QuadIso.measure_ball (lam : Measure K) [lam.IsAddLeftInvariant] {a c : K}
    (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1) (x : K) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    lam ((fun t => a * t + c * t ^ 2) ⁻¹' vball x γ ∩ {s | Valued.v s < 1}) =
      lam (vball x γ ∩ {s | Valued.v s < 1}) := by sorry
