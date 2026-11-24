-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_stSplit
-- name    : GlobalTheory.CompanionTheory.RgSplit.stSplit
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:53.667672+00:00
-- url     : https://prove2.me/theorems/ff0a40dc-a405-4f25-ac21-260f5ecc1369
-- title:
--   Rg Split: st Split
-- statement:
--   The Rg Split construction uses the st Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L310-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L310-L320

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgSplit

theorem GlobalTheory.CompanionTheory.RgSplit.stSplit : StSandwich → StPairing → StSplit := by sorry
