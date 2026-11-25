-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuReduce_cut_fderiv
-- name    : GlobalTheory.CompanionTheory.BmuReduce.cut_fderiv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:40:08.519854+00:00
-- url     : https://prove2.me/theorems/639765fe-ac97-5b5b-bdeb-dea925c7b75b
-- title:
--   Bmu Reduce: cut fderiv
-- statement:
--   The Bmu Reduce construction uses the cut fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L35-L40

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

theorem GlobalTheory.CompanionTheory.BmuReduce.cut_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (v : E) :
    ContDiff ℝ ∞ (fun t => fderiv ℝ φ t v) ∧ HasCompactSupport (fun t => fderiv ℝ φ t v) ∧
      tsupport (fun t => fderiv ℝ φ t v) ⊆ U := by sorry
