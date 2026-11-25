-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_X_withG
-- name    : GlobalTheory.UnitLemma.CayleyCase.X_withG
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:57:49.257295+00:00
-- url     : https://prove2.me/theorems/bc29d132-4a1f-44b7-9c15-88f28d172eeb
-- title:
--   Cayley Case: X with G
-- statement:
--   The Cayley Case construction uses the X with G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L228-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L228-L231

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

theorem GlobalTheory.UnitLemma.CayleyCase.X_withG (B : InvAlg K) (Y : B.A)
    (h : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) ↔ (∀ y ∈ L, Y * y ∈ L)) (x : B.A) :
    (withG B Y).X x = B.X x := by sorry
