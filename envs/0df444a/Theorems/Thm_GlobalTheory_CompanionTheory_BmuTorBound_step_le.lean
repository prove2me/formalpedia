-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorBound_step_le
-- name    : GlobalTheory.CompanionTheory.BmuTorBound.step_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:42:43.971527+00:00
-- url     : https://prove2.me/theorems/b77d8e23-e72a-46d1-8a30-d03684f77268
-- title:
--   Bmu Tor Bound: step le
-- statement:
--   The Bmu Tor Bound construction uses the step le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorBound.lean#L15-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorBound.lean#L15-L48

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

theorem GlobalTheory.CompanionTheory.BmuTorBound.step_le (k r : ℕ) (d : Fin (2 * r + k + 1) → ℝ) (M : ℝ) (hd : IsTor k r d) (hM : 1 ≤ M)
    (ha : ∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) (j : ℕ) (hj : j + 1 < 2 * r + k + 1) :
    d ⟨j, by omega⟩ ≤ M * d ⟨j + 1, hj⟩ := by sorry
