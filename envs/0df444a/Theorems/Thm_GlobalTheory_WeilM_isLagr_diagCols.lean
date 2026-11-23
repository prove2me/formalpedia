-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_isLagr_diagCols
-- name    : GlobalTheory.WeilM.isLagr_diagCols
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:54.155646+00:00
-- url     : https://prove2.me/theorems/1f76955b-7ab9-4110-8e64-b206229568de
-- title:
--   Weil M: is Lagr diag Cols
-- statement:
--   The Weil M construction uses the is Lagr diag Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L347-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L347-L360

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
variable (c)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]

theorem GlobalTheory.WeilM.isLagr_diagCols (JB : Matrix β β E) : IsLagr c (dbl JB) (diagCols β : Matrix (β ⊕ β) β E) := by sorry
