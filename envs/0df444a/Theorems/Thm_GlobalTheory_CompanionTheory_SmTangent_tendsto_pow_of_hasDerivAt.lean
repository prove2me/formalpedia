-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmTangent_tendsto_pow_of_hasDerivAt
-- name    : GlobalTheory.CompanionTheory.SmTangent.tendsto_pow_of_hasDerivAt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:21.404544+00:00
-- url     : https://prove2.me/theorems/93efeb5e-68e4-4d88-9e93-f1e1dee3da6f
-- title:
--   Sm Tangent: tendsto pow of has Deriv At
-- statement:
--   The Sm Tangent construction uses the tendsto pow of has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean#L48-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean#L48-L139

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
variable {A : Type*} [NormedRing A]
variable [NormedAlgebra ℝ A] [CompleteSpace A]

theorem GlobalTheory.CompanionTheory.SmTangent.tendsto_pow_of_hasDerivAt (h1 : ‖(1 : A)‖ ≤ 1) (γ : ℝ → A) (Y : A) (h0 : γ 0 = 1)
    (hd : HasDerivAt γ Y 0) (t : ℝ) :
    Tendsto (fun k : ℕ => γ (t / k) ^ k) atTop (𝓝 (NormedSpace.exp (t • Y))) := by sorry
