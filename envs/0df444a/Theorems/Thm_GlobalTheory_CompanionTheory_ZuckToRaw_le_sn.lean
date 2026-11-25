-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckToRaw_le_sn
-- name    : GlobalTheory.CompanionTheory.ZuckToRaw.le_sn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:55.766555+00:00
-- url     : https://prove2.me/theorems/74be2095-a340-4d6b-965f-f45fc55b9574
-- title:
--   Zuck To Raw: le sn
-- statement:
--   The Zuck To Raw construction uses the le sn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean#L69-L72

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ToRawComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckToRaw
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.ZuckToRaw.le_sn (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (x : M X) :
    ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖ ≤ sn X W x := by sorry
