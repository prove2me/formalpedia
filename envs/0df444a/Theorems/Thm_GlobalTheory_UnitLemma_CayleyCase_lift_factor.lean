-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_lift_factor
-- name    : GlobalTheory.UnitLemma.CayleyCase.lift_factor
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:54.44094+00:00
-- url     : https://prove2.me/theorems/2a40e9cf-3daf-4e30-ac8e-4dce14e6027e
-- title:
--   Cayley Case: lift factor
-- statement:
--   The Cayley Case construction uses the lift factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L199-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L199-L214

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

theorem GlobalTheory.UnitLemma.CayleyCase.lift_factor (B₁ B₂ : InvAlg K) (hsep : (B₁.P * B₂.P).Separable) (Q : K.O[X])
    (hQ : Q.map (algebraMap K.O K.E) = B₁.P * B₂.P) :
    ∃ Q₁ Q₂ : K.O[X], Q = Q₁ * Q₂ ∧ Q₁.map (algebraMap K.O K.E) = B₁.P ∧ Q₂.map (algebraMap K.O K.E) = B₂.P ∧
      aeval B₁.g Q₁ = 0 ∧ aeval B₂.g Q₂ = 0 ∧ Q.Monic := by sorry
