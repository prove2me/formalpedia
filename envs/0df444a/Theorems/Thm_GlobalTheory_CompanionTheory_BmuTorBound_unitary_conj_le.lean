-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorBound_unitary_conj_le
-- name    : GlobalTheory.CompanionTheory.BmuTorBound.unitary_conj_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:51:46.18571+00:00
-- url     : https://prove2.me/theorems/8093dc2e-830c-5678-aca0-279599dd3139
-- title:
--   Bmu Tor Bound: unitary conj le
-- statement:
--   The Bmu Tor Bound construction uses the unitary conj le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorBound.lean#L80-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorBound.lean#L80-L102

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix CompanionTheory.Bmu Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuTorBound
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem GlobalTheory.CompanionTheory.BmuTorBound.unitary_conj_le {n : ℕ} (R B : Mat n) (hR : Rᴴ * R = 1) : ‖Rᴴ * B * R‖ ≤ (n : ℝ) ^ 2 * ‖B‖ := by sorry
