-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_unitary_adapted_basis_apply_basis
-- name    : GlobalTheory.CompanionTheory.BmuAdapt.unitary_adapted_basis_apply_basis
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:42:42.435009+00:00
-- url     : https://prove2.me/theorems/efc35db2-8506-4467-ac27-6d24b807d765
-- title:
--   Bmu Adapt: unitary adapted basis apply basis
-- statement:
--   The Bmu Adapt construction uses the unitary adapted basis apply basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L141-L143

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
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

theorem GlobalTheory.CompanionTheory.BmuAdapt.unitary_adapted_basis_apply_basis (k r : ℕ) (j : Fin (2 * r + k + 1)) : G0 k r *ᵥ bvec j = col k r j := by sorry
