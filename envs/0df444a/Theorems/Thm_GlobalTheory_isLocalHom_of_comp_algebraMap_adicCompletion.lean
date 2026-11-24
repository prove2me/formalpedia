-- Prove2me | Theorems.Thm_GlobalTheory_isLocalHom_of_comp_algebraMap_adicCompletion
-- name    : GlobalTheory.isLocalHom_of_comp_algebraMap_adicCompletion
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:13.757801+00:00
-- url     : https://prove2.me/theorems/e444c760-4413-41a9-b4bb-c502da5072dc
-- title:
--   Global Theory: is Local Hom of comp algebra Map adic Completion
-- statement:
--   The Global Theory construction uses the is Local Hom of comp algebra Map adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L227-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L227-L233

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

theorem GlobalTheory.isLocalHom_of_comp_algebraMap_adicCompletion {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* B) (hg : g.comp (algebraMap A _) = f) :
    IsLocalHom g := by sorry
