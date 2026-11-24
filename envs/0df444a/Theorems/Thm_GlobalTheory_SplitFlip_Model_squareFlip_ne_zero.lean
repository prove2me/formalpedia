-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Model_squareFlip_ne_zero
-- name    : GlobalTheory.SplitFlip.Model.squareFlip_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:19:53.228568+00:00
-- url     : https://prove2.me/theorems/d38c9885-0541-4cbc-a30a-d26548caf6b9
-- title:
--   Model: square Flip ne zero
-- statement:
--   The Model construction uses the square Flip ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L148-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L148-L192

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
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitFlip.Model.squareFlip_ne_zero [IsEmpty A'] {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {e : ℕ} (he : 1 ≤ e) (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (P : Finset D) (Φ : Matrix A' D k → ℂ) (hΦ : Φ 0 ≠ 0) :
    squareFlip (haarVol (KO k A')) σ ψ ν ϖ e P Φ ≠ 0 := by sorry
