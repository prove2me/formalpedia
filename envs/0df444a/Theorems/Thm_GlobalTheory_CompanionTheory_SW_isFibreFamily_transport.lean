-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_isFibreFamily_transport
-- name    : GlobalTheory.CompanionTheory.SW.isFibreFamily_transport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:29.966722+00:00
-- url     : https://prove2.me/theorems/7c8284cc-2720-4eab-9e89-cc640e5679d5
-- title:
--   SW: is Fibre Family transport
-- statement:
--   The SW construction uses the is Fibre Family transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsFibreFamilyTransport.lean#L9-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsFibreFamilyTransport.lean#L9-L53

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsFibreFamilyTransport
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.isFibreFamily_transport :
    ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (V' : Type) [TopologicalSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V'] (f' : V' → Y) (g' : V' → X), Continuous g' → (∀ v, f' v = ι (g' v)) → ∀ (e : V ≃ₜ V') (τ : X ≃ₜ X), (∀ v, g' (e v) = τ (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (μ.map e) f' ι (g' ⁻¹' (τ '' B)) (ν.map τ) (τ '' B) (fun b => (fib (τ.symm b)).map e) := by sorry
