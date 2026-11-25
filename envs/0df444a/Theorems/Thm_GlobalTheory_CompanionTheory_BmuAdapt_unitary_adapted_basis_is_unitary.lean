-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_unitary_adapted_basis_is_unitary
-- name    : GlobalTheory.CompanionTheory.BmuAdapt.unitary_adapted_basis_is_unitary
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:18.883445+00:00
-- url     : https://prove2.me/theorems/90cab4fc-609c-48bd-915f-15919890d081
-- title:
--   Bmu Adapt: unitary adapted basis is unitary
-- statement:
--   The Bmu Adapt construction uses the unitary adapted basis is unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L152-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L152-L166

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

theorem GlobalTheory.CompanionTheory.BmuAdapt.unitary_adapted_basis_is_unitary (k r : ℕ) (hk : 1 ≤ k) : (G0 k r)ᴴ * G0 k r = 1 := by sorry
