-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorBound_chain_le
-- name    : GlobalTheory.CompanionTheory.BmuTorBound.chain_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:10.769914+00:00
-- url     : https://prove2.me/theorems/6e8f75cd-3738-45a4-93d4-9c38b8a6ed6e
-- title:
--   Bmu Tor Bound: chain le
-- statement:
--   The Bmu Tor Bound construction uses the chain le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorBound.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorBound.lean#L50-L60

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

theorem GlobalTheory.CompanionTheory.BmuTorBound.chain_le {n : ℕ} (d : Fin n → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hs : ∀ (j : ℕ) (hj : j + 1 < n), d ⟨j, by omega⟩ ≤ M * d ⟨j + 1, hj⟩) (j m : ℕ) (h : j + m < n) :
    d ⟨j, by omega⟩ ≤ M ^ m * d ⟨j + m, h⟩ := by sorry
