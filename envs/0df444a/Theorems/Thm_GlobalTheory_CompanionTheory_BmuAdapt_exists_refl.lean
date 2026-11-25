-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_exists_refl
-- name    : GlobalTheory.CompanionTheory.BmuAdapt.exists_refl
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:20:32.694798+00:00
-- url     : https://prove2.me/theorems/20e70191-197f-543f-b00a-9c39b4390916
-- title:
--   Bmu Adapt: exists refl
-- statement:
--   The Bmu Adapt construction uses the exists refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L74-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L74-L100

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

theorem GlobalTheory.CompanionTheory.BmuAdapt.exists_refl {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (u z : ι → ℂ) (huz : herm H u u = herm H z z)
    (hc : herm H u u - herm H u z ≠ 0) :
    ∃ γ : Matrix ι ι ℂ, γᴴ * H * γ = H ∧ γ *ᵥ u = z ∧
      ∀ x, herm H x u = 0 → herm H x z = 0 → γ *ᵥ x = x := by sorry
