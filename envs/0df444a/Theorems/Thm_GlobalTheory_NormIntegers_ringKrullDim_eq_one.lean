-- Prove2me | Theorems.Thm_GlobalTheory_NormIntegers_ringKrullDim_eq_one
-- name    : GlobalTheory.NormIntegers.ringKrullDim_eq_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:36:10.512419+00:00
-- url     : https://prove2.me/theorems/5e442cdc-a701-4bfd-851a-e50817ed7995
-- title:
--   Norm Integers: ring Krull Dim eq one
-- statement:
--   The Norm Integers construction uses the ring Krull Dim eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L192-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L192-L211

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

theorem GlobalTheory.NormIntegers.ringKrullDim_eq_one {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
    {O : Type*} [CommRing O] [Algebra O C] (hO : (NormedField.valuation (K := C)).Integers O) :
    ringKrullDim O = 1 := by sorry
