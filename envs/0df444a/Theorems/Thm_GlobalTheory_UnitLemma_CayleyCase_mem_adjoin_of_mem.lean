-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_mem_adjoin_of_mem
-- name    : GlobalTheory.UnitLemma.CayleyCase.mem_adjoin_of_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:51:07.994838+00:00
-- url     : https://prove2.me/theorems/f778ad15-c787-4a1b-97ee-e1729916bd18
-- title:
--   Cayley Case: mem adjoin of mem
-- statement:
--   The Cayley Case construction uses the mem adjoin of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L90-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L90-L97

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

theorem GlobalTheory.UnitLemma.CayleyCase.mem_adjoin_of_mem {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O E] [Algebra E A]
    [Algebra O A] [IsScalarTower O E A] {a z : A} (h : z ∈ Algebra.adjoin O ({a} : Set A)) :
    z ∈ Algebra.adjoin E ({a} : Set A) := by sorry
