-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_two_le
-- name    : GlobalTheory.CompanionTheory.BesselCartan.two_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:22:16.112201+00:00
-- url     : https://prove2.me/theorems/a31f4692-a71f-58ed-b93d-cfef2448f47b
-- title:
--   Bessel Cartan: two le
-- statement:
--   The Bessel Cartan construction uses the two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L153-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L153-L170

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

theorem GlobalTheory.CompanionTheory.BesselCartan.two_le (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1) (y : Fin n → ℂ)
    (h : star y ⬝ᵥ H *ᵥ y = -2) : ∃ N : ℝ, 2 ≤ N ∧ star y ⬝ᵥ y = N := by sorry
