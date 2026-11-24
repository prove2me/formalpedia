-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SpreadingModels_properSpreads
-- name    : GlobalTheory.CompanionTheory.SpreadingModels.properSpreads
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:43.557512+00:00
-- url     : https://prove2.me/theorems/24fb23f3-1dbe-42e4-aeb5-0321cb03e84d
-- title:
--   Spreading Models: proper Spreads
-- statement:
--   The Spreading Models construction uses the proper Spreads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L388-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L388-L420

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SpreadingModels
open GlobalTheory.CompanionTheory.Ultra

theorem GlobalTheory.CompanionTheory.SpreadingModels.properSpreads : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) := by sorry
