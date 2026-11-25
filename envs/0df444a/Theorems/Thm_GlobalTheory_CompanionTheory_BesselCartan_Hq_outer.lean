-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_Hq_outer
-- name    : GlobalTheory.CompanionTheory.BesselCartan.Hq_outer
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:41:55.574791+00:00
-- url     : https://prove2.me/theorems/0d306091-1b05-48e6-ae62-98f004a188a1
-- title:
--   Bessel Cartan: Hq outer
-- statement:
--   The Bessel Cartan construction uses the Hq outer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L207-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecomposition.lean#L207-L221

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

theorem GlobalTheory.CompanionTheory.BesselCartan.Hq_outer (k r : ℕ) (i j : Fin (2 * r + k + 1)) (hi : outer k r i) (hij : i.val + j.val = 2 * r + k) :
    Hq k r *ᵥ bvec j = bvec i := by sorry
