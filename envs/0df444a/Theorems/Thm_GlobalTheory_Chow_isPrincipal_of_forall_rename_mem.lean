-- Prove2me | Theorems.Thm_GlobalTheory_Chow_isPrincipal_of_forall_rename_mem
-- name    : GlobalTheory.Chow.isPrincipal_of_forall_rename_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:29.611006+00:00
-- url     : https://prove2.me/theorems/7f81937f-a753-4154-bfe7-8f20f3f906e5
-- title:
--   Chow: is Principal of forall rename mem
-- statement:
--   The Chow construction uses the is Principal of forall rename mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L73-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L73-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
import Theorems.Thm_GlobalTheory_Chow_IsBlockHomogeneous_rename

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.Chow.isPrincipal_of_forall_rename_mem {K ι ι' : Type*} [Field K] [Finite ι'] (ε : ι ≃ Option ι')
    (E : Ideal (MvPolynomial ι K)) [E.IsPrime]
    (h : ∀ g : MvPolynomial ι' K, rename (fun v => ε.symm (some v)) g ∈ E → g = 0) :
    E.IsPrincipal := by sorry
