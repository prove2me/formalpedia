-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICHWMap_diagOp_fst
-- name    : GlobalTheory.CompanionTheory.DSICHWMap.diagOp_fst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:00.535811+00:00
-- url     : https://prove2.me/theorems/dda86557-5bc3-4568-8125-5811f8cdb2d6
-- title:
--   DSICHWMap: diag Op fst
-- statement:
--   The DSICHWMap construction uses the diag Op fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HwMapOfLowSpan.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HwMapOfLowSpan.lean#L19-L20

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HwMapOfLowSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICHWMap
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
variable {T V : Type} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem GlobalTheory.CompanionTheory.DSICHWMap.diagOp_fst (A : Module.End ℂ T) (B : Module.End ℂ V) (x : WithLp 2 (T × V)) :
    (WithLp.ofLp (diagOp A B x)).1 = A (WithLp.ofLp x).1 := by sorry
