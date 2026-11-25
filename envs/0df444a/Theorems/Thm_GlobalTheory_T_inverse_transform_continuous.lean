-- Prove2me | Theorems.Thm_GlobalTheory_T_inverse_transform_continuous
-- name    : GlobalTheory.T.inverse_transform_continuous
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:16.237055+00:00
-- url     : https://prove2.me/theorems/3e665990-1ad0-4cc4-b974-2b28e82555fd
-- title:
--   T: inverse transform continuous
-- statement:
--   The T construction uses the inverse transform continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformContinuousStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformContinuousStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuous
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuousStatement
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

theorem GlobalTheory.T.inverse_transform_continuous : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] [FirstCountableTopology T] (φ : ℝ × ℝ → T → X), ExpDecay φ → Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) → Continuous (fun y : (ℂ × ℂ) × T => inv (fun t => φ t y.2) y.1) := by sorry
