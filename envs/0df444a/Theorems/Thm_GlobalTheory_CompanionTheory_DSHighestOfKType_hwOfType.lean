-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSHighestOfKType_hwOfType
-- name    : GlobalTheory.CompanionTheory.DSHighestOfKType.hwOfType
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:31.690955+00:00
-- url     : https://prove2.me/theorems/2d9a28d7-e974-4271-8700-24976b28d299
-- title:
--   DSHighest Of KType: hw Of Type
-- statement:
--   The DSHighest Of KType construction uses the hw Of Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NotCdomAddRoot.lean#L56-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NotCdomAddRoot.lean#L56-L69

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NotCdomAddRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSHighestOfKType
open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSHighestOfKType.hwOfType : CompanionTheory.D.DSIC.StabLink → CompanionTheory.D.DSIC.WtLink → CompanionTheory.D.DSIC.HWofType := by sorry
