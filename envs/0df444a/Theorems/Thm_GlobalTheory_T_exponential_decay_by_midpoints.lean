-- Prove2me | Theorems.Thm_GlobalTheory_T_exponential_decay_by_midpoints
-- name    : GlobalTheory.T.exponential_decay_by_midpoints
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:39:34.034096+00:00
-- url     : https://prove2.me/theorems/8b3ab787-5084-437d-88b2-2dddff944180
-- title:
--   T: exponential decay by midpoints
-- statement:
--   The T construction uses the exponential decay by midpoints property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialDecayByMidpointsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialDecayByMidpointsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialDecayByMidpoints
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialDecayByMidpointsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exponential_decay_by_midpoints : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X) (S : Set (ℝ × ℝ)), (∀ a ∈ S, ∀ g : T, ∃ r : ℝ, 0 < r ∧ ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ x : ℝ × ℝ, |x.1 - a.1| ≤ r → |x.2 - a.2| ≤ r → ∀ g' ∈ U, ∀ t : ℝ × ℝ, ‖φ t g'‖ ≤ M * Real.exp (-rdot x t)) → (∀ x : ℝ × ℝ, ∃ a ∈ S, ∃ b ∈ S, x = midpoint ℝ a b) → ExpDecay φ := by sorry
