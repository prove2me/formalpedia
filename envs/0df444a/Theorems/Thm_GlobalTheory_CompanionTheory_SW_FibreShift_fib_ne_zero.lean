-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreShift_fib_ne_zero
-- name    : GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:03:35.680332+00:00
-- url     : https://prove2.me/theorems/a4784253-dfd5-4e39-b50b-18c2936eea48
-- title:
--   Fibre Shift: fib ne zero
-- statement:
--   The Fibre Shift construction uses the fib ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationHaarBase.lean#L123-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationHaarBase.lean#L123-L152

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

theorem GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [ν.IsAddHaarMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U W : Set V), IsOpen W → W ⊆ U → W.Nonempty → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ T : X → V → V, (∀ s, Measurable (T s)) → (∀ s, μ.map (T s) = μ) → (∀ s, ContinuousOn (T s) W) → (∀ s v, T s v ∈ W ↔ v ∈ W) → (∀ s, ∀ v ∈ W, T (-s) (T s v) = v) → (∀ s, ∀ v ∈ W, g (T s v) = g v + s) → ∀ b : X, fib b ≠ 0 := by sorry
