-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatrixLie_hasDerivAt_exp_mul_exp_of_finiteDimensional
-- name    : GlobalTheory.CompanionTheory.MatrixLie.hasDerivAt_exp_mul_exp_of_finiteDimensional
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:53:42.316426+00:00
-- url     : https://prove2.me/theorems/90b2dab7-998a-4b8f-8db7-bd701f4c6f6d
-- title:
--   Matrix Lie: has Deriv At exp mul exp of finite Dimensional
-- statement:
--   The Matrix Lie construction uses the has Deriv At exp mul exp of finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HasDerivAtExpMulExpOfFiniteDimensional.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HasDerivAtExpMulExpOfFiniteDimensional.lean#L11-L19

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurveStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtExpMulExpOfFiniteDimensional
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatrixLie

theorem GlobalTheory.CompanionTheory.MatrixLie.hasDerivAt_exp_mul_exp_of_finiteDimensional {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y)) (X + Y) 0 := by sorry
