-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckToRaw_one_coord
-- name    : GlobalTheory.CompanionTheory.ZuckToRaw.one_coord
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:56.360553+00:00
-- url     : https://prove2.me/theorems/923107d2-3743-495f-950f-5e402dc6fcad
-- title:
--   Zuck To Raw: one coord
-- statement:
--   The Zuck To Raw construction uses the one coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean#L98-L101

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

theorem GlobalTheory.CompanionTheory.ZuckToRaw.one_coord {U : URep k r} {Y : Obj k r} (f : M (one U) →ₗ[ℂ] M Y) (d : Y.1.ι) (x : M (one U)) :
    extZ (coord f d ()) (x () : U.R.H) = (f x d : Y.2.R.H) := by sorry
