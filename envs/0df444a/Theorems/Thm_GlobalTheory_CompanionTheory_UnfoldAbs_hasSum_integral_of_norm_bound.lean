-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnfoldAbs_hasSum_integral_of_norm_bound
-- name    : GlobalTheory.CompanionTheory.UnfoldAbs.hasSum_integral_of_norm_bound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:40.563856+00:00
-- url     : https://prove2.me/theorems/45eac43d-692e-44a2-8d23-9319e2c55eb0
-- title:
--   Unfold Abs: has Sum integral of norm bound
-- statement:
--   The Unfold Abs construction uses the has Sum integral of norm bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainFourierUnfolding.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainFourierUnfolding.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFourierUnfolding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnfoldAbs

theorem GlobalTheory.CompanionTheory.UnfoldAbs.hasSum_integral_of_norm_bound {A Z : Type} [MeasurableSpace A] (μ : Measure A)
    [IsFiniteMeasure μ] [Countable Z] (G : Z → A → ℂ)
    (hm : ∀ q, AEStronglyMeasurable (G q) μ) (M : ℝ)
    (hb : ∀ b, Summable (fun q => ‖G q b‖) ∧ ∑' q, ‖G q b‖ ≤ M) :
    HasSum (fun q => ∫ b, G q b ∂μ) (∫ b, ∑' q, G q b ∂μ) := by sorry
