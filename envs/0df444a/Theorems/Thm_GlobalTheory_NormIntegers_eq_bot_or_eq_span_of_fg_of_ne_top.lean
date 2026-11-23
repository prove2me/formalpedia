-- Prove2me | Theorems.Thm_GlobalTheory_NormIntegers_eq_bot_or_eq_span_of_fg_of_ne_top
-- name    : GlobalTheory.NormIntegers.eq_bot_or_eq_span_of_fg_of_ne_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:42.264834+00:00
-- url     : https://prove2.me/theorems/18b0a9f9-55a5-4c54-a1dd-43e3c5f06a3d
-- title:
--   Norm Integers: eq bot or eq span of fg of ne top
-- statement:
--   The Norm Integers construction uses the eq bot or eq span of fg of ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L112-L120

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

theorem GlobalTheory.NormIntegers.eq_bot_or_eq_span_of_fg_of_ne_top {J : Ideal O} (hJ : J.FG) (hJ' : J ≠ ⊤) :
    J = ⊥ ∨ ∃ w : O, 0 < ‖algebraMap O C w‖ ∧ ‖algebraMap O C w‖ < 1 ∧ J = Ideal.span {w} := by sorry
