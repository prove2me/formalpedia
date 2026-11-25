-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_Hq_sq
-- name    : GlobalTheory.CompanionTheory.BesselCartan.Hq_sq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:19:20.858725+00:00
-- url     : https://prove2.me/theorems/4b28e900-25fa-559a-892f-f1c47bcc6c11
-- title:
--   Bessel Cartan: Hq sq
-- statement:
--   The Bessel Cartan construction uses the Hq sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L239-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L239-L262

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

theorem GlobalTheory.CompanionTheory.BesselCartan.Hq_sq (k r : ℕ) : Hq k r * Hq k r = 1 := by sorry
