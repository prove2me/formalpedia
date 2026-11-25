-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckHomCat_sn_add_le
-- name    : GlobalTheory.CompanionTheory.ZuckHomCat.sn_add_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:29:33.323899+00:00
-- url     : https://prove2.me/theorems/6d62e0ec-7749-4939-b24f-8bc22a076c36
-- title:
--   Zuck Hom Cat: sn add le
-- statement:
--   The Zuck Hom Cat construction uses the sn add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L19-L26

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

theorem GlobalTheory.CompanionTheory.ZuckHomCat.sn_add_le (X : Obj k r) {W : List (Mx k r)} (hW : LieWd k r W) (x y : M X) :
    sn X W (x + y) ≤ sn X W x + sn X W y := by sorry
