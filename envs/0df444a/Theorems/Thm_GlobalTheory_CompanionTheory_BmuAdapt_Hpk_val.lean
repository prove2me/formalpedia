-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_Hpk_val
-- name    : GlobalTheory.CompanionTheory.BmuAdapt.Hpk_val
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:37:17.60404+00:00
-- url     : https://prove2.me/theorems/174bb945-4540-419d-9dfe-1d361306f253
-- title:
--   Bmu Adapt: Hpk val
-- statement:
--   The Bmu Adapt construction uses the Hpk val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L172-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean#L172-L177

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

theorem GlobalTheory.CompanionTheory.BmuAdapt.Hpk_val (i j : Fin (2 * r + k + 1)) : Hpk k r i j =
    if i.val < r ∧ i.val + j.val = 2 * r + k then 1
    else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
    else if r ≤ i.val ∧ i.val ≤ r + k ∧ i.val = j.val then (if i.val = r + k then -1 else 1)
    else 0 := by sorry
