-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICKExp_kExp
-- name    : GlobalTheory.CompanionTheory.DSICKExp.kExp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:45:30.614881+00:00
-- url     : https://prove2.me/theorems/44f0fc36-9839-4fe3-a1da-0cfeeb906036
-- title:
--   DSICKExp: k Exp
-- statement:
--   The DSICKExp construction uses the k Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KExp.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KExp.lean#L9-L12

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactExponentialSurjective
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KExp
import Theorems.Thm_Formalism_REAL_kExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKExp

theorem GlobalTheory.CompanionTheory.DSICKExp.kExp : CompanionTheory.D.DSIC.KExp := by sorry
