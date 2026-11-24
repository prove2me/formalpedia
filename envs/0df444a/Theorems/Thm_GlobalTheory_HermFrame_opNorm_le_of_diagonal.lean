-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_opNorm_le_of_diagonal
-- name    : GlobalTheory.HermFrame.opNorm_le_of_diagonal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:27.283864+00:00
-- url     : https://prove2.me/theorems/0d988319-b349-4303-bf1b-19a64b9c477f
-- title:
--   Herm Frame: op Norm le of diagonal
-- statement:
--   The Herm Frame construction uses the op Norm le of diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L290-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L290-L320

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]

theorem GlobalTheory.HermFrame.opNorm_le_of_diagonal {H : Matrix n n ℂ} {G : Matrix m m ℂ} (hH : H.PosDef)
    (hG : G.PosSemidef) {F : (m → ℂ) → (m → ℂ) → Matrix n n ℂ} (hF : IsSesq F)
    (hs : ∀ ξ v w, form H (F ξ ξ *ᵥ v) w = form H v (F ξ ξ *ᵥ w)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ξ v, ‖form H (F ξ ξ *ᵥ v) v‖ ≤ C * gnorm G ξ ^ 2 * gnorm H v ^ 2) (ξ η : m → ℂ) :
    opNorm H H (F ξ η) ≤ 2 * C * gnorm G ξ * gnorm G η := by sorry
