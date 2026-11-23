-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_isHermitian_quotGram
-- name    : GlobalTheory.HermFrame.isHermitian_quotGram
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:41.825799+00:00
-- url     : https://prove2.me/theorems/f4126a48-5c99-4ae1-93de-50b5f2864381
-- title:
--   Herm Frame: is Hermitian quot Gram
-- statement:
--   The Herm Frame construction uses the is Hermitian quot Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L428-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L428-L434

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
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}
omit [Fintype l] [DecidableEq l]

theorem GlobalTheory.HermFrame.isHermitian_quotGram (h : H.IsHermitian) : (quotGram H).IsHermitian := by sorry
