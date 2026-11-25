-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckHomCat_sn_nonneg
-- name    : GlobalTheory.CompanionTheory.ZuckHomCat.sn_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:13.875873+00:00
-- url     : https://prove2.me/theorems/48b2688e-80e4-5122-a7f2-2447314c1ed0
-- title:
--   Zuck Hom Cat: sn nonneg
-- statement:
--   The Zuck Hom Cat construction uses the sn nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L16-L17

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

theorem GlobalTheory.CompanionTheory.ZuckHomCat.sn_nonneg (X : Obj k r) (W : List (Mx k r)) (x : M X) : 0 ≤ sn X W x := by sorry
