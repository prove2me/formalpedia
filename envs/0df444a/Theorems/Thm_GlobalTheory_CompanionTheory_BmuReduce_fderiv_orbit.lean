-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuReduce_fderiv_orbit
-- name    : GlobalTheory.CompanionTheory.BmuReduce.fderiv_orbit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:34:11.547254+00:00
-- url     : https://prove2.me/theorems/a4e01fdb-aed2-5f50-9d32-596f36a591b4
-- title:
--   Bmu Reduce: fderiv orbit
-- statement:
--   The Bmu Reduce construction uses the fderiv orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L103-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L103-L115

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

theorem GlobalTheory.CompanionTheory.BmuReduce.fderiv_orbit [CompleteSpace H] (hder : DsDer) {Hm : Mat n} (hσ : URep Hm σ)
    {W : List (Mat n)} (hW : LieWd Hm W) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : E → Mat n}
    (hs : ContDiff ℝ ∞ s) (hm : ∀ t, s t ∈ UH Hm) {t v : E} {Z : Mat n} (hZ : Lie Hm Z)
    (hfl : ∀ τ : ℝ, s (t + τ • v) = s t * ex Z τ) {u : H} (hu : IsSm (UH Hm) σ u) :
    fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t v = dsW σ W (σ (s t) (ds σ Z u)) := by sorry
