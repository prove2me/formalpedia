-- Prove2me | Theorems.Thm_GlobalTheory_T_measurable_embedding_of_injective_proper
-- name    : GlobalTheory.T.measurable_embedding_of_injective_proper
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:01.616979+00:00
-- url     : https://prove2.me/theorems/f1d0838e-3552-5844-965c-351a2c2799a4
-- title:
--   T: measurable embedding of injective proper
-- statement:
--   The T construction uses the measurable embedding of injective proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableEmbeddingOfInjectiveProperStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableEmbeddingOfInjectiveProperStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableEmbeddingOfInjectiveProper
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableEmbeddingOfInjectiveProperStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.measurable_embedding_of_injective_proper : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (W : Set V), IsOpen W → ∀ (B B' : Set X), IsOpen B → IsOpen B' → B' ⊆ B → ∀ fib fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B ∩ W) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B' ∩ W) ν B' fib' → ∀ b ∈ B', fib' b = fib b := by sorry
