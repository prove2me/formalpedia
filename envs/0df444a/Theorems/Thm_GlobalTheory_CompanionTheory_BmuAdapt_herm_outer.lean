-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_herm_outer
-- name    : GlobalTheory.CompanionTheory.BmuAdapt.herm_outer
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:27.132001+00:00
-- url     : https://prove2.me/theorems/f1db4099-d03f-518a-8e62-34b1ac47c3a2
-- title:
--   Bmu Adapt: herm outer
-- statement:
--   The Bmu Adapt construction uses the herm outer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L301-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L301-L312

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

theorem GlobalTheory.CompanionTheory.BmuAdapt.herm_outer (k r : ℕ) (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val)
    (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : herm (Hpk k r) (bvec i) z = 0 := by sorry
