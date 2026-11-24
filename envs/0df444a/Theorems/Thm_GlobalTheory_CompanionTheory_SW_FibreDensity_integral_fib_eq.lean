-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_integral_fib_eq
-- name    : GlobalTheory.CompanionTheory.SW.FibreDensity.integral_fib_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:03:48.546708+00:00
-- url     : https://prove2.me/theorems/775ba066-c22e-4a99-8ad9-201ceb090aab
-- title:
--   Fibre Density: integral fib eq
-- statement:
--   The Fibre Density construction uses the integral fib eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityUnique.lean#L120-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityUnique.lean#L120-L125

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreDensity
variable {V X Y : Type}
  [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {B : Set X}
  {fib : X → Measure V}

theorem GlobalTheory.CompanionTheory.SW.FibreDensity.integral_fib_eq (hfin : ∀ b, IsLocallyFiniteMeasure (fib b)) {ψ : V → ℂ}
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) (b : X) :
    ∫ v, ψ v ∂(fib b) = ((∫ v, (ψ v).re ∂(fib b) : ℝ) : ℂ)
      + ((∫ v, (ψ v).im ∂(fib b) : ℝ) : ℂ) * Complex.I := by sorry
