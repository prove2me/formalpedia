-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_norm_conj_rootE
-- name    : GlobalTheory.CompanionTheory.BmuRootVec.norm_conj_rootE
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:27:09.474404+00:00
-- url     : https://prove2.me/theorems/f6d5857b-a85e-487e-a705-2c9b11911c12
-- title:
--   Bmu Root Vec: norm conj root E
-- statement:
--   The Bmu Root Vec construction uses the norm conj root E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/RootVectors.lean#L138-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/RootVectors.lean#L138-L154

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuRootVec
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.BmuRootVec.norm_conj_rootE {R : Mat (2 * r + k + 1)} (hR : Rᴴ * R = 1) (a : Fin r) (κ : ℂ) :
    ‖Rᴴ * rootE k r a κ * R‖ ≤ 2 * ‖κ‖ := by sorry
