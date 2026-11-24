-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FibreDensityLimit_lintegral_slice
-- name    : GlobalTheory.CompanionTheory.FibreDensityLimit.lintegral_slice
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:36.615977+00:00
-- url     : https://prove2.me/theorems/6a01561d-6102-4f7d-b509-7d596c3ddacf
-- title:
--   Fibre Density Limit: lintegral slice
-- statement:
--   The Fibre Density Limit construction uses the lintegral slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationInjectiveOpenMap.lean#L113-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationInjectiveOpenMap.lean#L113-L140

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationInjectiveOpenMap
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibreDensityLimit
open Set
variable {V X Y : Type} [MeasurableSpace V] [TopologicalSpace V] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem GlobalTheory.CompanionTheory.FibreDensityLimit.lintegral_slice (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hUm : MeasurableSet U)
    (hι : Function.Injective ι) (hg : Measurable g) (hfg : ∀ v, f v = ι (g v)) {w : V → ℝ≥0∞}
    (hw : Measurable w) (hw0 : ∀ v, v ∉ U → w v = 0) {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ v in f ⁻¹' (ι '' A), w v ∂μ = ∫⁻ s in A, ∫⁻ v, w v ∂(fib s) ∂ν := by sorry
