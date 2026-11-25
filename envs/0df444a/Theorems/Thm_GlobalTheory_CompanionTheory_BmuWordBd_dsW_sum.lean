-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuWordBd_dsW_sum
-- name    : GlobalTheory.CompanionTheory.BmuWordBd.dsW_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:21:28.359643+00:00
-- url     : https://prove2.me/theorems/9cf80483-bd0f-44d8-a464-ea922612c1d7
-- title:
--   Bmu Word Bd: ds W sum
-- statement:
--   The Bmu Word Bd construction uses the ds W sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WordLengthBoundOfLinear.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WordLengthBoundOfLinear.lean#L53-L64

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordLengthBoundOfLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuWordBd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem GlobalTheory.CompanionTheory.BmuWordBd.dsW_sum {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)}
    {σ : Mat n → (H →L[ℂ] H)} (h : RepOn G σ) {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i, IsSm G σ (v i)) {W : List (Mat n)} (hW : LieW G W) :
    IsSm G σ (∑ i ∈ s, v i) ∧ dsW σ W (∑ i ∈ s, v i) = ∑ i ∈ s, dsW σ W (v i) := by sorry
