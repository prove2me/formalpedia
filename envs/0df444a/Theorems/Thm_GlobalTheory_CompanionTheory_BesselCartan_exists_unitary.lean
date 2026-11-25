-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_exists_unitary
-- name    : GlobalTheory.CompanionTheory.BesselCartan.exists_unitary
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:21:50.195463+00:00
-- url     : https://prove2.me/theorems/f01a497e-09b2-4ae6-8eab-bae63d61cfdf
-- title:
--   Bessel Cartan: exists unitary
-- statement:
--   The Bessel Cartan construction uses the exists unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L78-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L78-L151

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCartan
open scoped ComplexOrder
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.BesselCartan.exists_unitary (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1) (x y : Fin n → ℂ)
    (h1 : star x ⬝ᵥ x = star y ⬝ᵥ y) (h2 : star x ⬝ᵥ H *ᵥ x = star y ⬝ᵥ H *ᵥ y) :
    ∃ K : Matrix (Fin n) (Fin n) ℂ, Kᴴ * K = 1 ∧ H * K = K * H ∧ K *ᵥ x = y ∧
      ∀ w, star x ⬝ᵥ w = 0 → star y ⬝ᵥ w = 0 → star x ⬝ᵥ H *ᵥ w = 0 → star y ⬝ᵥ H *ᵥ w = 0 → K *ᵥ w = w := by sorry
