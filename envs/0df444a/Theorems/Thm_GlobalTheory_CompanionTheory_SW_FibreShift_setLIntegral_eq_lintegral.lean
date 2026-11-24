-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreShift_setLIntegral_eq_lintegral
-- name    : GlobalTheory.CompanionTheory.SW.FibreShift.setLIntegral_eq_lintegral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:03:36.105379+00:00
-- url     : https://prove2.me/theorems/060f2d5e-5e6f-44d0-9b22-0900654d8a5b
-- title:
--   Fibre Shift: set LIntegral eq lintegral
-- statement:
--   The Fibre Shift construction uses the set LIntegral eq lintegral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationHaarBase.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationHaarBase.lean#L47-L55

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationHaarBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreShift

theorem GlobalTheory.CompanionTheory.SW.FibreShift.setLIntegral_eq_lintegral {V : Type} [MeasurableSpace V] {μ : Measure V} {W : Set V}
    (hW : MeasurableSet W) {a : V → ℝ≥0∞} (ha : ∀ v, v ∉ W → a v = 0) :
    ∫⁻ v in W, a v ∂μ = ∫⁻ v, a v ∂μ := by sorry
