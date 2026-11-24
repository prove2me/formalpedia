-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Model_omA_unip_fourier
-- name    : GlobalTheory.SplitFlip.Model.omA_unip_fourier
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:20:05.588213+00:00
-- url     : https://prove2.me/theorems/658ae64a-298e-404e-b72f-fa51aebd8bb7
-- title:
--   Model: om A unip fourier
-- statement:
--   The Model construction uses the om A unip fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L290-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L290-L316

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

theorem GlobalTheory.SplitFlip.Model.omA_unip_fourier (ψ : AddChar k Circle) (m : Measure k) (ν β : kˣ →* ℂˣ) (b : Matrix D₁ D₂ k)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) :
    omA ν β 1 (unip b) (fourierInt ψ m (Assignment.one.block D₁ D₂) Φ) =
      fourierInt ψ m (Assignment.one.block D₁ D₂)
        fun T => (ψ (-trace (T.toCols₁ * b * T.toCols₂ᵀ)) : ℂ) * Φ T := by sorry
