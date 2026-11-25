-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_col_q
-- name    : GlobalTheory.CompanionTheory.BmuAdapt.col_q
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:38:44.667117+00:00
-- url     : https://prove2.me/theorems/96d2a675-488f-5e88-a3ed-51c93e09366d
-- title:
--   Bmu Adapt: col q
-- statement:
--   The Bmu Adapt construction uses the col q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L230-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L230-L232

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuAdapt
variable {k r : ℕ} {i j : Fin (2 * r + k + 1)}

theorem GlobalTheory.CompanionTheory.BmuAdapt.col_q (hk : 1 ≤ k) (hj : j.val = r + k) :
    col k r j = s2 • (bvec (wI k r 0) - bvec (wI k r (Fin.last k))) := by sorry
