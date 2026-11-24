-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreShift_continuous_lintegral
-- name    : GlobalTheory.CompanionTheory.SW.FibreShift.continuous_lintegral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:04:01.164632+00:00
-- url     : https://prove2.me/theorems/54dbfea0-3cec-4f84-98f8-c19ee0dd20e5
-- title:
--   Fibre Shift: continuous lintegral
-- statement:
--   The Fibre Shift construction uses the continuous lintegral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationHaarBase.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationHaarBase.lean#L35-L45

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

theorem GlobalTheory.CompanionTheory.SW.FibreShift.continuous_lintegral {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y}
    {ι : X → Y} {U : Set V} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) {φ : V → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (h0 : ∀ v, 0 ≤ φ v) :
    Continuous fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by sorry
