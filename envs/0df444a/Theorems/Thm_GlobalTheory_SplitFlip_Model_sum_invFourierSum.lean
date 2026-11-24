-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Model_sum_invFourierSum
-- name    : GlobalTheory.SplitFlip.Model.sum_invFourierSum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:19:53.0358+00:00
-- url     : https://prove2.me/theorems/515c7b9e-2d58-4fc2-822d-9805e17ac0eb
-- title:
--   Model: sum inv Fourier Sum
-- statement:
--   The Model construction uses the sum inv Fourier Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L94-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L94-L144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

theorem GlobalTheory.SplitFlip.Model.sum_invFourierSum {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) (Ψ : Matrix A D k → ℂ) (X : Matrix A D k) (S₀ : A → P → Res k e) :
    ∑ T : A → P → Res k e, invFourierSum ψ ϖ e P Ψ (setCols P X (liftRes T)) *
      (ψ (pairCols P (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) (liftRes T)) : ℂ) =
      (Fintype.card (Res k e) : ℂ) ^ (Fintype.card A * P.card) * Ψ (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) := by sorry
