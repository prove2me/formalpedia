-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_isContDensityOn_fibreIntegral
-- name    : GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:43.680801+00:00
-- url     : https://prove2.me/theorems/5d234089-d13d-4c09-bc56-ecbd2629641a
-- title:
--   Fibre Density: is Cont Density On fibre Integral
-- statement:
--   The Fibre Density construction uses the is Cont Density On fibre Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityUnique.lean#L211-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityUnique.lean#L211-L257

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

theorem GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral : ∀ (V X Y : Type) [TopologicalSpace V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y)
    (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) →
    ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V,
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib →
    ∀ φ : V → ℂ, Continuous φ → HasCompactSupport φ →
    HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B φ (fun b => ∫ v, φ v ∂(fib b)) ∧
      ∀ b, Integrable φ (fib b) := by sorry
