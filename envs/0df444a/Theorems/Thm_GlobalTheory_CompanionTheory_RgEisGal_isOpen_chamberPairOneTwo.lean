-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_chamberPairOneTwo
-- name    : GlobalTheory.CompanionTheory.RgEisGal.isOpen_chamberPairOneTwo
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:58:04.002907+00:00
-- url     : https://prove2.me/theorems/e261c4cf-a09e-4a26-ba52-57cf38c635f5
-- title:
--   Rg Eis Gal: is Open chamber Pair One Two
-- statement:
--   The Rg Eis Gal construction uses the is Open chamber Pair One Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L123-L126

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

theorem GlobalTheory.CompanionTheory.RgEisGal.isOpen_chamberPairOneTwo (M : ℝ) : IsOpen (chamberPairOneTwo M) := by sorry
