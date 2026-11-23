-- Prove2me | Theorems.Thm_GlobalTheory_NormIntegers_isAdicComplete_of_fg
-- name    : GlobalTheory.NormIntegers.isAdicComplete_of_fg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:54.882294+00:00
-- url     : https://prove2.me/theorems/1b72be3b-146b-4373-b50f-77365ff3857c
-- title:
--   Norm Integers: is Adic Complete of fg
-- statement:
--   The Norm Integers construction uses the is Adic Complete of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L147-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
open GlobalTheory.NormIntegers
variable {C : Type*} [NormedField C] [IsUltrametricDist C] {O : Type*} [CommRing O] [Algebra O C]
  (hO : (NormedField.valuation (K := C)).Integers O)
include hO

theorem GlobalTheory.NormIntegers.isAdicComplete_of_fg [CompleteSpace C] {J : Ideal O} (hJ : J.FG) (hJ' : J ≠ ⊤) :
    IsAdicComplete J O := by sorry
