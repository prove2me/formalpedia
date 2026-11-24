-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_exists_isFibreFamily_openOrbit
-- name    : GlobalTheory.CompanionTheory.SW.Slice.exists_isFibreFamily_openOrbit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:35.429952+00:00
-- url     : https://prove2.me/theorems/b68486b4-aa81-42e0-b6c5-a4e627c298a4
-- title:
--   Slice: exists is Fibre Family open Orbit
-- statement:
--   The Slice construction uses the exists is Fibre Family open Orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L403-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L403-L417

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice

theorem GlobalTheory.CompanionTheory.SW.Slice.exists_isFibreFamily_openOrbit : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [SecondCountableTopology Q] [T2Space Q] [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X], (∀ (q : Q) (v : V), g (q • v) = q • g v) → ∀ (χ χ' : Q →* ℝ≥0), Continuous χ → Continuous χ' → (∀ q : Q, μ.map (fun v => q • v) = χ q • μ) → (∀ q : Q, ν.map (fun x => q • x) = χ' q • ν) → ∀ b₀ : X, IsOpenEmbedding (fun q : Q => q • b₀) → ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' (Set.range fun q : Q => q • b₀)) ν (Set.range fun q : Q => q • b₀) fib := by sorry
