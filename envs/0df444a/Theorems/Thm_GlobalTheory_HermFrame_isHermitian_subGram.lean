-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_isHermitian_subGram
-- name    : GlobalTheory.HermFrame.isHermitian_subGram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:47.248893+00:00
-- url     : https://prove2.me/theorems/6d2e71df-d211-442b-9933-7d906b111bc1
-- title:
--   Herm Frame: is Hermitian sub Gram
-- statement:
--   The Herm Frame construction uses the is Hermitian sub Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L419-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L419-L419

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
omit [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem GlobalTheory.HermFrame.isHermitian_subGram (h : H.IsHermitian) : (subGram H).IsHermitian := by sorry
