-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_dg_rootE
-- name    : GlobalTheory.CompanionTheory.BmuRootVec.dg_rootE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:21:33.919803+00:00
-- url     : https://prove2.me/theorems/da3cd076-7460-580b-bd30-fb5675c9d12d
-- title:
--   Bmu Root Vec: dg root E
-- statement:
--   The Bmu Root Vec construction uses the dg root E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/RootVectors.lean#L111-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/RootVectors.lean#L111-L136

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

theorem GlobalTheory.CompanionTheory.BmuRootVec.dg_rootE {d : Fin (2 * r + k + 1) → ℝ} (hd : IsTor k r d) (a : Fin r) (κ : ℂ) :
    dg d * rootE k r a κ = ((d (eI k r a) / d (nxt k r a) : ℝ) : ℂ) • (rootE k r a κ * dg d) := by sorry
