-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuReduce_lieW_of
-- name    : GlobalTheory.CompanionTheory.BmuReduce.lieW_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:35:15.857954+00:00
-- url     : https://prove2.me/theorems/1a72703d-2e14-5157-b627-4d3d131470f9
-- title:
--   Bmu Reduce: lie W of
-- statement:
--   The Bmu Reduce construction uses the lie W of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L67-L68

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

theorem GlobalTheory.CompanionTheory.BmuReduce.lieW_of {Hm : Mat n} {W : List (Mat n)} (hW : LieWd Hm W) : LieW (UH Hm) W := by sorry
