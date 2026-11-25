-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_N_withG
-- name    : GlobalTheory.UnitLemma.CayleyCase.N_withG
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:08.822598+00:00
-- url     : https://prove2.me/theorems/f15ad057-af4a-4522-a178-8871a12919be
-- title:
--   Cayley Case: N with G
-- statement:
--   The Cayley Case construction uses the N with G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L233-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L233-L238

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
variable {K : UQ}

theorem GlobalTheory.UnitLemma.CayleyCase.N_withG (B : InvAlg K) (Y : B.A)
    (h : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) ↔ (∀ y ∈ L, Y * y ∈ L)) (x : B.A) :
    (withG B Y).N x = B.N x := by sorry
