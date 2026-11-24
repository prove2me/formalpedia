-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmTangent_tangent_mem_lieAlg
-- name    : GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:17.021751+00:00
-- url     : https://prove2.me/theorems/ef5ddf12-9101-4ce4-816c-82771d13953f
-- title:
--   Sm Tangent: tangent mem lie Alg
-- statement:
--   The Sm Tangent construction uses the tangent mem lie Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean#L161-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean#L161-L175

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

theorem GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg : ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G →
    ∀ (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 →
      (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ G) → HasDerivAt γ Y 0 → Y ∈ lieAlg G := by sorry
