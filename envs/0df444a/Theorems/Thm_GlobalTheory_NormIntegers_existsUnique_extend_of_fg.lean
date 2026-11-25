-- Prove2me | Theorems.Thm_GlobalTheory_NormIntegers_existsUnique_extend_of_fg
-- name    : GlobalTheory.NormIntegers.existsUnique_extend_of_fg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:36:14.645973+00:00
-- url     : https://prove2.me/theorems/6bbe741c-7183-4507-a65f-8b854063b348
-- title:
--   Norm Integers: exists Unique extend of fg
-- statement:
--   The Norm Integers construction uses the exists Unique extend of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L162-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L162-L169

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

theorem GlobalTheory.NormIntegers.existsUnique_extend_of_fg [CompleteSpace C] {A : Type*} [CommRing A] [IsLocalRing A]
    (hA : (IsLocalRing.maximalIdeal A).FG) (f : A →+* O) [IsLocalHom f] :
    ∃! g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* O,
      g.comp (algebraMap A _) = f := by sorry
