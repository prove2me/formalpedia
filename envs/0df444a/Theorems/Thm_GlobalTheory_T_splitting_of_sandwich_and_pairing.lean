-- Prove2me | Theorems.Thm_GlobalTheory_T_splitting_of_sandwich_and_pairing
-- name    : GlobalTheory.T.splitting_of_sandwich_and_pairing
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:39:49.208115+00:00
-- url     : https://prove2.me/theorems/f52655e0-de2c-43b9-a1c3-ba235dbe4d9f
-- title:
--   T: splitting of sandwich and pairing
-- statement:
--   The T construction uses the splitting of sandwich and pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.splitting_of_sandwich_and_pairing : StSandwich → StPairing → StSplit := by sorry
