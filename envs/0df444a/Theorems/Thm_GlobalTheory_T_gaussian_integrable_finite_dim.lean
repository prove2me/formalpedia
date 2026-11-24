-- Prove2me | Theorems.Thm_GlobalTheory_T_gaussian_integrable_finite_dim
-- name    : GlobalTheory.T.gaussian_integrable_finite_dim
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:40:38.620625+00:00
-- url     : https://prove2.me/theorems/755114bd-4283-434c-8b40-7f7960b021c0
-- title:
--   T: gaussian integrable finite dim
-- statement:
--   The T construction uses the gaussian integrable finite dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianIntegrableFiniteDimStatement.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianIntegrableFiniteDimStatement.lean#L5-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianIntegrableFiniteDim
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianIntegrableFiniteDimStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.gaussian_integrable_finite_dim : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c →
    MeasureTheory.Integrable (fun y : ι → ℝ => Real.exp (-(c * ∑ i, y i ^ 2))) := by sorry
