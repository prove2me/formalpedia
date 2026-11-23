-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICHWMap_sum_ext
-- name    : GlobalTheory.CompanionTheory.DSICHWMap.sum_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:43.589866+00:00
-- url     : https://prove2.me/theorems/7fe992ef-cfbe-4e2b-86a7-6d70d25458fb
-- title:
--   DSICHWMap: sum ext
-- statement:
--   The DSICHWMap construction uses the sum ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HwMapOfLowSpan.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HwMapOfLowSpan.lean#L25-L28

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

theorem GlobalTheory.CompanionTheory.DSICHWMap.sum_ext {x y : WithLp 2 (T × V)} (h1 : (WithLp.ofLp x).1 = (WithLp.ofLp y).1)
    (h2 : (WithLp.ofLp x).2 = (WithLp.ofLp y).2) : x = y := by sorry
