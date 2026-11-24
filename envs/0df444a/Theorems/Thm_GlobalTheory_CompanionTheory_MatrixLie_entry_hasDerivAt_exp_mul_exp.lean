-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatrixLie_entry_hasDerivAt_exp_mul_exp
-- name    : GlobalTheory.CompanionTheory.MatrixLie.entry_hasDerivAt_exp_mul_exp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:53:30.871814+00:00
-- url     : https://prove2.me/theorems/987ce7d8-b728-4e97-bff8-2d1268f1ba95
-- title:
--   Matrix Lie: entry has Deriv At exp mul exp
-- statement:
--   The Matrix Lie construction uses the entry has Deriv At exp mul exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HasDerivAtExpMulExpOfFiniteDimensional.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HasDerivAtExpMulExpOfFiniteDimensional.lean#L27-L37

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

theorem GlobalTheory.CompanionTheory.MatrixLie.entry_hasDerivAt_exp_mul_exp {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ =>
      (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y)) i j) ((X + Y) i j) 0 := by sorry
