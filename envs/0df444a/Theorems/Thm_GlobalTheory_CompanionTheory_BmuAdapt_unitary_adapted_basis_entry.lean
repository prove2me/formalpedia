-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_unitary_adapted_basis_entry
-- name    : GlobalTheory.CompanionTheory.BmuAdapt.unitary_adapted_basis_entry
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:38:50.668893+00:00
-- url     : https://prove2.me/theorems/fa9455a0-ff5c-5aeb-8d47-0e6df40dce94
-- title:
--   Bmu Adapt: unitary adapted basis entry
-- statement:
--   The Bmu Adapt construction uses the unitary adapted basis entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L148-L150

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

theorem GlobalTheory.CompanionTheory.BmuAdapt.unitary_adapted_basis_entry (k r : ℕ) (H : Mat (2 * r + k + 1)) (i j : Fin (2 * r + k + 1)) :
    ((G0 k r)ᴴ * H * G0 k r) i j = herm H (col k r j) (col k r i) := by sorry
