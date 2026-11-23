-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_tt_anti
-- name    : GlobalTheory.CompanionTheory.DSNormLt.tt_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:39.4376+00:00
-- url     : https://prove2.me/theorems/3fb01f45-ca6d-4fa7-bbdf-ff2016e8759a
-- title:
--   DSNorm Lt: tt anti
-- statement:
--   The DSNorm Lt construction uses the tt anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L158-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L158-L159

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSNormLt.tt_anti {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : tt A b a = - tt A a b := by sorry
