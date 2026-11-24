-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Eis_line_tube_convex
-- name    : GlobalTheory.CompanionTheory.Eis.line_tube_convex
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:36:41.126619+00:00
-- url     : https://prove2.me/theorems/77c08630-57c4-46a3-a734-32f95fadde88
-- title:
--   Eis: line tube convex
-- statement:
--   The Eis construction uses the line tube convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IdentityTubeHolds.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IdentityTubeHolds.lean#L13-L25

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

theorem GlobalTheory.CompanionTheory.Eis.line_tube_convex {Ω : Set (ℝ × ℝ)} (hc : Convex ℝ Ω) (p v : ℂ × ℂ) :
    Convex ℝ {τ : ℂ | p + τ • v ∈ tube Ω} := by sorry
