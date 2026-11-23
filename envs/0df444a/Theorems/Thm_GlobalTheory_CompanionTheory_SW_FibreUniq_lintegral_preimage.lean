-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_lintegral_preimage
-- name    : GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:37.955222+00:00
-- url     : https://prove2.me/theorems/80fe2d8b-135d-4a83-9c81-2df069491a85
-- title:
--   Fibre Uniq: lintegral preimage
-- statement:
--   The Fibre Uniq construction uses the lintegral preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityExists.lean#L78-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityExists.lean#L78-L109

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

theorem GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → Y} {g : V → X} {ι : X → Y} (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) {O U : Set V} {B : Set X} {fib : X → Measure V}
    (hO : IsOpen O) (hU : O ⊆ U) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ O → φ v = 0)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v in O, (g ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by sorry
