-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Eis_tube_isOpen
-- name    : GlobalTheory.CompanionTheory.Eis.tube_isOpen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:05.737253+00:00
-- url     : https://prove2.me/theorems/8a32045f-8f1e-448a-80df-5ae171d017fd
-- title:
--   Eis: tube is Open
-- statement:
--   The Eis construction uses the tube is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IdentityTubeHolds.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IdentityTubeHolds.lean#L8-L11

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdentityTubeHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Eis

theorem GlobalTheory.CompanionTheory.Eis.tube_isOpen {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) : IsOpen (tube Ω) := by sorry
