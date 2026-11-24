-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_exists_dyadic_bound
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.exists_dyadic_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:23:40.381076+00:00
-- url     : https://prove2.me/theorems/a16a5a2c-2660-4304-a3e9-c57a1e2bb14e
-- title:
--   Real Tail: exists dyadic bound
-- statement:
--   The Real Tail construction uses the exists dyadic bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBall.lean#L19-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBall.lean#L19-L54

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
variable {P ι : Type} [Fintype P] [Fintype ι]

theorem GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.exists_dyadic_bound (f : (P → ι → ℝ) → ℝ) (N : ℕ) (K : ℝ) (x : P → ι → ℝ)
    (hf : 0 ≤ f x) (hx : f x * (1 + ∑ w, ‖x w‖) ^ N ≤ K) :
    ∃ j : ℕ, x ∈ (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)) ∧
      f x ≤ K * 2 ^ N * (1 / 2) ^ (j * N) := by sorry
