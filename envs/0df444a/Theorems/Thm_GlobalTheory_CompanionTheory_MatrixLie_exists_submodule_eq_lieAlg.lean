-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatrixLie_exists_submodule_eq_lieAlg
-- name    : GlobalTheory.CompanionTheory.MatrixLie.exists_submodule_eq_lieAlg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:53:35.923482+00:00
-- url     : https://prove2.me/theorems/55169b15-6ec4-43f5-aa7b-96557f5605c5
-- title:
--   Matrix Lie: exists submodule eq lie Alg
-- statement:
--   The Matrix Lie construction uses the exists submodule eq lie Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HasDerivAtExpMulExpOfFiniteDimensional.lean#L44-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HasDerivAtExpMulExpOfFiniteDimensional.lean#L44-L70

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

theorem GlobalTheory.CompanionTheory.MatrixLie.exists_submodule_eq_lieAlg :
    ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G →
      ∃ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
        (S : Set (Matrix (Fin n) (Fin n) ℂ)) = lieAlg G := by sorry
