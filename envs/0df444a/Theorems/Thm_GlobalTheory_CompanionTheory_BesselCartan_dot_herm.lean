-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_dot_herm
-- name    : GlobalTheory.CompanionTheory.BesselCartan.dot_herm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:10:28.786094+00:00
-- url     : https://prove2.me/theorems/953bcdc0-28af-57d9-92e5-82447c922cc2
-- title:
--   Bessel Cartan: dot herm
-- statement:
--   The Bessel Cartan construction uses the dot herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L74-L76

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

theorem GlobalTheory.CompanionTheory.BesselCartan.dot_herm (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (x w : Fin n → ℂ) :
    star (H *ᵥ x) ⬝ᵥ w = star x ⬝ᵥ H *ᵥ w := by sorry
