-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_continuousOn_fib
-- name    : GlobalTheory.CompanionTheory.SW.FibreDensity.continuousOn_fib
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:11.02653+00:00
-- url     : https://prove2.me/theorems/1a4f0853-0392-4462-8646-7fd6373b5f0d
-- title:
--   Fibre Density: continuous On fib
-- statement:
--   The Fibre Density construction uses the continuous On fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityUnique.lean#L145-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityUnique.lean#L145-L156

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

theorem GlobalTheory.CompanionTheory.SW.FibreDensity.continuousOn_fib (hfin : ∀ b, IsLocallyFiniteMeasure (fib b))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    {ψ : V → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ g ⁻¹' B) :
    ContinuousOn (fun b => ∫ v, ψ v ∂(fib b)) B := by sorry
