-- Prove2me | Theorems.Thm_GlobalTheory_T_pairing_of_sandwich_statement
-- name    : GlobalTheory.T.pairing_of_sandwich_statement
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:53.584435+00:00
-- url     : https://prove2.me/theorems/c0b98d1e-f0eb-4840-8879-e4fb8d87f84f
-- title:
--   T: pairing of sandwich statement
-- statement:
--   The T construction uses the pairing of sandwich statement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatementStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatementStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatementStatement
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

theorem GlobalTheory.T.pairing_of_sandwich_statement : StSandwich → StPairing := by sorry
