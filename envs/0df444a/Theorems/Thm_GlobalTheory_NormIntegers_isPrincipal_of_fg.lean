-- Prove2me | Theorems.Thm_GlobalTheory_NormIntegers_isPrincipal_of_fg
-- name    : GlobalTheory.NormIntegers.isPrincipal_of_fg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:53.1868+00:00
-- url     : https://prove2.me/theorems/6c7c08d3-9bad-408e-b9a3-36d82af94895
-- title:
--   Norm Integers: is Principal of fg
-- statement:
--   The Norm Integers construction uses the is Principal of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L107-L110

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

theorem GlobalTheory.NormIntegers.isPrincipal_of_fg {J : Ideal O} (hJ : J.FG) : J.IsPrincipal := by sorry
