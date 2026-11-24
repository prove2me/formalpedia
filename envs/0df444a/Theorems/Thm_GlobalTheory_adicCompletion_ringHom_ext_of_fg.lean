-- Prove2me | Theorems.Thm_GlobalTheory_adicCompletion_ringHom_ext_of_fg
-- name    : GlobalTheory.adicCompletion_ringHom_ext_of_fg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:57.739408+00:00
-- url     : https://prove2.me/theorems/5773fb92-1cc7-4baf-9e68-edca9134e862
-- title:
--   Global Theory: adic Completion ring Hom ext of fg
-- statement:
--   The Global Theory construction uses the adic Completion ring Hom ext of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L27-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L27-L47

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
variable {A B : Type*} [CommRing A] [CommRing B]

theorem GlobalTheory.adicCompletion_ringHom_ext_of_fg (I : Ideal A) (hI : I.FG) (f : A →+* B)
    [IsHausdorff (I.map f) B] {g₁ g₂ : AdicCompletion I A →+* B}
    (h₁ : g₁.comp (algebraMap A _) = f) (h₂ : g₂.comp (algebraMap A _) = f) : g₁ = g₂ := by sorry
