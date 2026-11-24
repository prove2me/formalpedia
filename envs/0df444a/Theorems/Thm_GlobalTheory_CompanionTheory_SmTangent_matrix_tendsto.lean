-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmTangent_matrix_tendsto
-- name    : GlobalTheory.CompanionTheory.SmTangent.matrix_tendsto
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:28.844649+00:00
-- url     : https://prove2.me/theorems/57077bf6-8ef9-4f9b-a30b-a415fa35b077
-- title:
--   Sm Tangent: matrix tendsto
-- statement:
--   The Sm Tangent construction uses the matrix tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean#L143-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean#L143-L159

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurve
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmTangent

theorem GlobalTheory.CompanionTheory.SmTangent.matrix_tendsto (n : ℕ) (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : γ 0 = 1) (hd : HasDerivAt γ Y 0) (t : ℝ) :
    Tendsto (fun k : ℕ => γ (t / k) ^ k) atTop (𝓝 (NormedSpace.exp ((t : ℂ) • Y))) := by sorry
