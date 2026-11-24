-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_convex_Om3
-- name    : GlobalTheory.CompanionTheory.RgEisGal.isOpen_convex_Om3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:03.708752+00:00
-- url     : https://prove2.me/theorems/ccd4a34e-f1d9-4ccb-b063-c5bbceecd823
-- title:
--   Rg Eis Gal: is Open convex Om3
-- statement:
--   The Rg Eis Gal construction uses the is Open convex Om3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L100-L103

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

theorem GlobalTheory.CompanionTheory.RgEisGal.isOpen_convex_Om3 (N r : ℝ) : IsOpen (Om3 N r) ∧ Convex ℝ (Om3 N r) := by sorry
