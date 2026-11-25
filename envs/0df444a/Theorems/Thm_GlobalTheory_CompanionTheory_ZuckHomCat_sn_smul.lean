-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckHomCat_sn_smul
-- name    : GlobalTheory.CompanionTheory.ZuckHomCat.sn_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:16.951409+00:00
-- url     : https://prove2.me/theorems/26bfff83-da20-44ad-94a3-6fef8df0d235
-- title:
--   Zuck Hom Cat: sn smul
-- statement:
--   The Zuck Hom Cat construction uses the sn smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L28-L35

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HomCategory
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckHomCat
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.ZuckHomCat.sn_smul (X : Obj k r) {W : List (Mx k r)} (hW : LieWd k r W) (a : ℂ) (x : M X) :
    sn X W (a • x) = ‖a‖ * sn X W x := by sorry
