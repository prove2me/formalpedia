-- Prove2me | Theorems.Thm_GlobalTheory_T_near_identity_matrix_positive_solution
-- name    : GlobalTheory.T.near_identity_matrix_positive_solution
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:53:53.347119+00:00
-- url     : https://prove2.me/theorems/8d1ad263-0e20-47b8-836b-d0d6acfeaeb0
-- title:
--   T: near identity matrix positive solution
-- statement:
--   The T construction uses the near identity matrix positive solution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NearIdentityMatrixPositiveSolutionStatement.lean#L5-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NearIdentityMatrixPositiveSolutionStatement.lean#L5-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NearIdentityMatrixPositiveSolution
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NearIdentityMatrixPositiveSolutionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.near_identity_matrix_positive_solution : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ, (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
    (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
    ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) → (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by sorry
