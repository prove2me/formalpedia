-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_convex_Om4
-- name    : GlobalTheory.CompanionTheory.RgEisGal.isOpen_convex_Om4
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:58:31.632026+00:00
-- url     : https://prove2.me/theorems/f22a31de-1e9e-466b-a4ee-5f4bc68937fa
-- title:
--   Rg Eis Gal: is Open convex Om4
-- statement:
--   The Rg Eis Gal construction uses the is Open convex Om4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L105-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L105-L121

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

theorem GlobalTheory.CompanionTheory.RgEisGal.isOpen_convex_Om4 (N r : ℝ) : IsOpen (Om4 N r) ∧ Convex ℝ (Om4 N r) := by sorry
