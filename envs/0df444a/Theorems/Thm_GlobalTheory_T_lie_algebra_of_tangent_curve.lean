-- Prove2me | Theorems.Thm_GlobalTheory_T_lie_algebra_of_tangent_curve
-- name    : GlobalTheory.T.lie_algebra_of_tangent_curve
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:51:41.247338+00:00
-- url     : https://prove2.me/theorems/3a01bc7e-c433-4852-9194-09f709e8d806
-- title:
--   T: lie algebra of tangent curve
-- statement:
--   The T construction uses the lie algebra of tangent curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurveStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurveStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurve
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lie_algebra_of_tangent_curve : ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G → ∀ (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 → (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ G) → HasDerivAt γ Y 0 → Y ∈ lieAlg G := by sorry
