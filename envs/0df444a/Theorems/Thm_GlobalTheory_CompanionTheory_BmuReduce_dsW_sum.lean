-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuReduce_dsW_sum
-- name    : GlobalTheory.CompanionTheory.BmuReduce.dsW_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:21:57.622811+00:00
-- url     : https://prove2.me/theorems/268814ab-b1e4-5a23-a611-307c7e185ea5
-- title:
--   Bmu Reduce: ds W sum
-- statement:
--   The Bmu Reduce construction uses the ds W sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L54-L65

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ReductionOfDerivedSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuReduce
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem GlobalTheory.CompanionTheory.BmuReduce.dsW_sum (h : RepOn G σ) {W : List (Mat n)} (hW : LieW G W) {ι : Type*} (c : ι → ℂ) (v : ι → H)
    (hv : ∀ i, IsSm G σ (v i)) (S : Finset ι) :
    IsSm G σ (∑ i ∈ S, c i • v i) ∧ dsW σ W (∑ i ∈ S, c i • v i) = ∑ i ∈ S, c i • dsW σ W (v i) := by sorry
