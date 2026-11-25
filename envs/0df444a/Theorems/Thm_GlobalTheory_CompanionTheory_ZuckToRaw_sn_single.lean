-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckToRaw_sn_single
-- name    : GlobalTheory.CompanionTheory.ZuckToRaw.sn_single
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:40.62103+00:00
-- url     : https://prove2.me/theorems/d23ff8d0-96d5-4105-be7c-a41b12fc6799
-- title:
--   Zuck To Raw: sn single
-- statement:
--   The Zuck To Raw construction uses the sn single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean#L60-L67

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

theorem GlobalTheory.CompanionTheory.ZuckToRaw.sn_single (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (v : X.2.R.smSub) :
    sn X W (Pi.single c v) = ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (v : X.2.R.H)‖ := by sorry
