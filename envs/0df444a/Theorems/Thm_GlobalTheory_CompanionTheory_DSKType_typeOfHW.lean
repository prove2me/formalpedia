-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSKType_typeOfHW
-- name    : GlobalTheory.CompanionTheory.DSKType.typeOfHW
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:32.978223+00:00
-- url     : https://prove2.me/theorems/511e4b32-aace-4e46-af13-9d6fb89bbc28
-- title:
--   DSKType: type Of HW
-- statement:
--   The DSKType construction uses the type Of HW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KsetSubsetUjset.lean#L20-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KsetSubsetUjset.lean#L20-L60

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KsetSubsetUjset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSKType
open CompanionTheory.D.DSIC PI.UpqRep

theorem GlobalTheory.CompanionTheory.DSKType.typeOfHW (hL : LowSpan) (hS : StabLink) (hW : WtLink) : TypeOfHW := by sorry
