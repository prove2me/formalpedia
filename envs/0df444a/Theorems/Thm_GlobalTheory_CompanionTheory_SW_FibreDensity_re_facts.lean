-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_re_facts
-- name    : GlobalTheory.CompanionTheory.SW.FibreDensity.re_facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:17.748094+00:00
-- url     : https://prove2.me/theorems/30ee7af4-8419-460b-9c0d-28412ad2a2b6
-- title:
--   Fibre Density: re facts
-- statement:
--   The Fibre Density construction uses the re facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityUnique.lean#L127-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityUnique.lean#L127-L134

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

theorem GlobalTheory.CompanionTheory.SW.FibreDensity.re_facts {ψ : V → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    {U : Set V} (hsupp : tsupport ψ ⊆ U) :
    Continuous (fun v => (ψ v).re) ∧ HasCompactSupport (fun v => (ψ v).re) ∧
      tsupport (fun v => (ψ v).re) ⊆ U := by sorry
