-- Prove2me | Theorems.Thm_GlobalTheory_T_approximate_identity_product_bumps
-- name    : GlobalTheory.T.approximate_identity_product_bumps
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:26:49.31924+00:00
-- url     : https://prove2.me/theorems/ed0f254a-6a3e-5228-8a13-91e84ada9f8b
-- title:
--   T: approximate identity product bumps
-- statement:
--   The T construction uses the approximate identity product bumps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ApproximateIdentityProductBumpsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ApproximateIdentityProductBumpsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ApproximateIdentityProductBumps
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ApproximateIdentityProductBumpsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.approximate_identity_product_bumps : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [T2Space A] [Fintype ι] (e : G ≃ₜ+ (ι → A)) (ρ : ℕ → A → ℝ), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ ∀ y, 0 ≤ ρ k y) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : A)).smallSets → (∀ k, Continuous (fun T : G => ∏ i, ρ k (e T i)) ∧ HasCompactSupport (fun T : G => ∏ i, ρ k (e T i)) ∧ ∀ T : G, 0 ≤ ∏ i, ρ k (e T i)) ∧ Filter.Tendsto (fun k => tsupport (fun T : G => ∏ i, ρ k (e T i))) Filter.atTop (nhds (0 : G)).smallSets := by sorry
