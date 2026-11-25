-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuReduce_parts
-- name    : GlobalTheory.CompanionTheory.BmuReduce.parts
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:22:13.485806+00:00
-- url     : https://prove2.me/theorems/169ce1b4-4088-4775-986f-dd7ebeadf2cd
-- title:
--   Bmu Reduce: parts
-- statement:
--   The Bmu Reduce construction uses the parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L121-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L121-L128

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

theorem GlobalTheory.CompanionTheory.BmuReduce.parts {d : ℕ} {ψ : (Fin d → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {f : (Fin d → ℝ) → H} (hf : ContDiff ℝ ∞ f) (v : Fin d → ℝ) :
    ∫ t, ψ t • fderiv ℝ f t v = - ∫ t, fderiv ℝ ψ t v • f t := by sorry
