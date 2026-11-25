-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_mem_adjoin_both
-- name    : GlobalTheory.UnitLemma.CayleyCase.mem_adjoin_both
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:54:55.51654+00:00
-- url     : https://prove2.me/theorems/2333ee00-7a15-4db5-a02b-566a3c298c48
-- title:
--   Cayley Case: mem adjoin both
-- statement:
--   The Cayley Case construction uses the mem adjoin both property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L39-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L39-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase

theorem GlobalTheory.UnitLemma.CayleyCase.mem_adjoin_both {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (g Y : A) (s ε : O) (Q : O[X])
    (hQm : Q.Monic) (hQ : aeval g Q = 0) (hQs : IsUnit (Q.eval (-s))) (hs : IsUnit s) (hε : IsUnit ε)
    (h2 : IsUnit (2 : O))
    (hY : Y * (g + algebraMap O A s) = algebraMap O A ε * (g - algebraMap O A s)) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by sorry
