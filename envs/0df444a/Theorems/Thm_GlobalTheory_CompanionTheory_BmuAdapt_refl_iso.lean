-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_refl_iso
-- name    : GlobalTheory.CompanionTheory.BmuAdapt.refl_iso
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:22:53.054894+00:00
-- url     : https://prove2.me/theorems/678ac061-104f-4401-9892-4cf9c594ee32
-- title:
--   Bmu Adapt: refl iso
-- statement:
--   The Bmu Adapt construction uses the refl iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L61-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L61-L72

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

theorem GlobalTheory.CompanionTheory.BmuAdapt.refl_iso {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (v : ι → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hvv : herm H v v = c + star c) (x y : ι → ℂ) :
    herm H (x - (c⁻¹ * herm H x v) • v) (y - (c⁻¹ * herm H y v) • v) = herm H x y := by sorry
