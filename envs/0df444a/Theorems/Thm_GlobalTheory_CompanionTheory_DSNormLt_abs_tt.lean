-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_abs_tt
-- name    : GlobalTheory.CompanionTheory.DSNormLt.abs_tt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:10.60551+00:00
-- url     : https://prove2.me/theorems/845408b9-8d80-408d-86b8-4f7a8f28d8b2
-- title:
--   DSNorm Lt: abs tt
-- statement:
--   The DSNorm Lt construction uses the abs tt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L176-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean#L176-L188

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

theorem GlobalTheory.CompanionTheory.DSNormLt.abs_tt {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : |tt A a b| ≤ 1 := by sorry
