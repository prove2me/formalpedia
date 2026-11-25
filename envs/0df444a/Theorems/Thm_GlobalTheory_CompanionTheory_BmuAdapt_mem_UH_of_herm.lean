-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_mem_UH_of_herm
-- name    : GlobalTheory.CompanionTheory.BmuAdapt.mem_UH_of_herm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:22:29.980838+00:00
-- url     : https://prove2.me/theorems/4eacb25b-40bb-49f2-b42b-80c1cf49db95
-- title:
--   Bmu Adapt: mem UH of herm
-- statement:
--   The Bmu Adapt construction uses the mem UH of herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L56-L59

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_herm

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuAdapt
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.BmuAdapt.mem_UH_of_herm {H g : Matrix ι ι ℂ} (h : ∀ x y, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) :
    gᴴ * H * g = H := by sorry
