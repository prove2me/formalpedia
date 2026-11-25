-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Model_omA_unip_fourier_inv
-- name    : GlobalTheory.SplitFlip.Model.omA_unip_fourier_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:30.816298+00:00
-- url     : https://prove2.me/theorems/8293ceb1-d4a0-56b1-bcbd-e6c222d9740f
-- title:
--   Model: om A unip fourier inv
-- statement:
--   The Model construction uses the om A unip fourier inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L318-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L318-L324

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
variable {A D₁ D₂ : Type*} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitFlip.Model.omA_unip_fourier_inv (ψ : AddChar k Circle) (m : Measure k) (ν β : kˣ →* ℂˣ) (b : Matrix D₁ D₂ k)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) :
    omA ν β 1 (unip b) (fourierInt ψ⁻¹ m (Assignment.one.block D₁ D₂) Φ) =
      fourierInt ψ⁻¹ m (Assignment.one.block D₁ D₂)
        fun T => (ψ (trace (T.toCols₁ * b * T.toCols₂ᵀ)) : ℂ) * Φ T := by sorry
