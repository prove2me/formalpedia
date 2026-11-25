-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuReduce_last_letter
-- name    : GlobalTheory.CompanionTheory.BmuReduce.last_letter
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:31:22.318549+00:00
-- url     : https://prove2.me/theorems/3c5ba263-109a-5a1d-a499-40f46dde5405
-- title:
--   Bmu Reduce: last letter
-- statement:
--   The Bmu Reduce construction uses the last letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L77-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ReductionOfDerivedSeries.lean#L77-L101

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

theorem GlobalTheory.CompanionTheory.BmuReduce.last_letter [CompleteSpace H] (hlin : DsLin) (had : DsAd) {Hm : Mat n} (hσ : URep Hm σ)
    {W : List (Mat n)} (hW : LieWd Hm W) {Y y : Mat n} (hY : Lie Hm Y) (hy : y ∈ UH Hm) {d e : ℕ}
    {Z : Fin d → Mat n} {Q : Fin e → Mat n} (hZ : ∀ j, Lie Hm (Z j)) (hQ : ∀ i, Lie Hm (Q i))
    {a : Fin d → ℝ} {b : Fin e → ℝ} (hab : y⁻¹ * Y * y = ∑ j, (a j : ℂ) • Z j + ∑ i, (b i : ℂ) • Q i)
    {u : H} (hu : IsSm (UH Hm) σ u) :
    dsW σ (W ++ [Y]) (σ y u) =
      ∑ j, a j • dsW σ W (σ y (ds σ (Z j) u)) + ∑ i, b i • dsW σ W (σ y (ds σ (Q i) u)) := by sorry
