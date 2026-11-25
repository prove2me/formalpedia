-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_exists_refl
-- name    : GlobalTheory.CompanionTheory.BesselCartan.exists_refl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:22:05.301226+00:00
-- url     : https://prove2.me/theorems/47192623-ef5e-4117-9228-8b72a1a8ac48
-- title:
--   Bessel Cartan: exists refl
-- statement:
--   The Bessel Cartan construction uses the exists refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L17-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L17-L72

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

theorem GlobalTheory.CompanionTheory.BesselCartan.exists_refl (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (ε : ℂ) (hε : star ε = ε) (a b : Fin n → ℂ)
    (ha : H *ᵥ a = ε • a) (hb : H *ᵥ b = ε • b) (hab : star a ⬝ᵥ a = star b ⬝ᵥ b) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ H * U = U * H ∧ U *ᵥ a = b ∧
      ∀ w, star a ⬝ᵥ w = 0 → star b ⬝ᵥ w = 0 → U *ᵥ w = w := by sorry
