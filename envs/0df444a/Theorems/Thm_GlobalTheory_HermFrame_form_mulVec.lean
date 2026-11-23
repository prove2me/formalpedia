-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_form_mulVec
-- name    : GlobalTheory.HermFrame.form_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:34.488829+00:00
-- url     : https://prove2.me/theorems/6692565c-65cc-43f0-b6da-2e567f1d23ac
-- title:
--   Herm Frame: form mul Vec
-- statement:
--   The Herm Frame construction uses the form mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L61-L64

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

theorem GlobalTheory.HermFrame.form_mulVec (K : Matrix n n ℂ) (A : Matrix n m ℂ) (B : Matrix n l ℂ) (u : m → ℂ)
    (w : l → ℂ) : form K (A *ᵥ u) (B *ᵥ w) = u ⬝ᵥ (Aᵀ * K * Bᴴᵀ) *ᵥ star w := by sorry
