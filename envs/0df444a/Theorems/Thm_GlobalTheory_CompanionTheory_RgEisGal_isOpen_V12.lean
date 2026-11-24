-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_V12
-- name    : GlobalTheory.CompanionTheory.RgEisGal.isOpen_V12
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:58:56.232813+00:00
-- url     : https://prove2.me/theorems/bd00e781-1251-4b20-a682-fb4ba6cc5503
-- title:
--   Rg Eis Gal: is Open V12
-- statement:
--   The Rg Eis Gal construction uses the is Open V12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L128-L131

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal

theorem GlobalTheory.CompanionTheory.RgEisGal.isOpen_V12 (M : ℝ) : IsOpen (chamberPairTwoThree M) := by sorry
