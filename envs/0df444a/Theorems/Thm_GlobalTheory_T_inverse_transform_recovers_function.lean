-- Prove2me | Theorems.Thm_GlobalTheory_T_inverse_transform_recovers_function
-- name    : GlobalTheory.T.inverse_transform_recovers_function
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:14.910422+00:00
-- url     : https://prove2.me/theorems/e8833a67-0e9f-4d55-bfec-c7911baf9bcf
-- title:
--   T: inverse transform recovers function
-- statement:
--   The T construction uses the inverse transform recovers function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformRecoversFunctionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformRecoversFunctionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunction
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunctionStatement
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

theorem GlobalTheory.T.inverse_transform_recovers_function : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (G : ℂ × ℂ → X) (x : ℝ × ℝ), Continuous (fun y => G (pt x y)) → (∃ M : ℝ, ∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) → Continuous (phi G x) → (∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))) → ∀ y : ℝ × ℝ, inv (phi G x) (pt x y) = G (pt x y) := by sorry
