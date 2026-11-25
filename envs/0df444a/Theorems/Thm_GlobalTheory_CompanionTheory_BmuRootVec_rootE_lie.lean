-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_rootE_lie
-- name    : GlobalTheory.CompanionTheory.BmuRootVec.rootE_lie
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:25:44.421645+00:00
-- url     : https://prove2.me/theorems/16f01018-39c2-5156-a520-20375b87064d
-- title:
--   Bmu Root Vec: root E lie
-- statement:
--   The Bmu Root Vec construction uses the root E lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/RootVectors.lean#L87-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/RootVectors.lean#L87-L99

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

theorem GlobalTheory.CompanionTheory.BmuRootVec.rootE_lie (a : Fin r) (κ : ℂ) : Lie (Hq k r) (rootE k r a κ) := by sorry
