-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_sub_inv_mem
-- name    : GlobalTheory.UnitLemma.CayleyCase.sub_inv_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:09.768328+00:00
-- url     : https://prove2.me/theorems/aeb703f3-af49-4621-96dd-dc3465ba658c
-- title:
--   Cayley Case: sub inv mem
-- statement:
--   The Cayley Case construction uses the sub inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L14-L28

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

theorem GlobalTheory.UnitLemma.CayleyCase.sub_inv_mem {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (a : A) (c : O) (p : O[X])
    (hp : aeval a p = 0) (hc : IsUnit (p.eval c)) :
    ∃ w ∈ Algebra.adjoin O ({a} : Set A), (a - algebraMap O A c) * w = 1 := by sorry
