-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_fibreFamily_eq
-- name    : GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:29.695417+00:00
-- url     : https://prove2.me/theorems/50d1fc97-ce67-4b0f-bbba-1d8d57fe90e4
-- title:
--   Fibre Uniq: fibre Family eq
-- statement:
--   The Fibre Uniq construction uses the fibre Family eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityExists.lean#L111-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityExists.lean#L111-L150

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreUniq

theorem GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (B B' : Set X) (hB : IsOpen B) (hB' : IsOpen B') (hBB : B' ⊆ B)
    (fib fib' : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    (h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B') ν B' fib')
    (b : X) (hb : b ∈ B') : fib' b = fib b := by sorry
