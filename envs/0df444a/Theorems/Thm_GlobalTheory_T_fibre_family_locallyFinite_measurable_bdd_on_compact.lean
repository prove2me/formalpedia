-- Prove2me | Theorems.Thm_GlobalTheory_T_fibre_family_locallyFinite_measurable_bdd_on_compact
-- name    : GlobalTheory.T.fibre_family_locallyFinite_measurable_bdd_on_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:48:18.566537+00:00
-- url     : https://prove2.me/theorems/05269693-4ac2-469f-b912-e65f773b58a8
-- title:
--   T: fibre family locally Finite measurable bdd on compact
-- statement:
--   The T construction uses the fibre family locally Finite measurable bdd on compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuousStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuousStatement.lean#L8-L9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fibre_family_locallyFinite_measurable_bdd_on_compact : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → (∀ b, IsLocallyFiniteMeasure (fib b)) ∧ (∀ b, b ∉ B → fib b = 0) ∧ (∀ A : Set V, MeasurableSet A → Measurable fun b => fib b A) ∧ ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B → ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by sorry
