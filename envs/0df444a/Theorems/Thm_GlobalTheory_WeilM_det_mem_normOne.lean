-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_det_mem_normOne
-- name    : GlobalTheory.WeilM.det_mem_normOne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:27.578326+00:00
-- url     : https://prove2.me/theorems/e8a916b8-41fe-4a49-acf3-988bac437fec
-- title:
--   Weil M: det mem norm One
-- statement:
--   The Weil M construction uses the det mem norm One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L312-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L312-L320

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

theorem GlobalTheory.WeilM.det_mem_normOne {ι : Type} [Fintype ι] [DecidableEq ι] {J : Matrix ι ι E} (hJ : IsHerm c J) (g : UG c J) :
    Matrix.GeneralLinearGroup.det (g : GL ι E) ∈ normOne c := by sorry
