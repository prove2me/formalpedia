-- Prove2me | Theorems.Thm_GlobalTheory_T_isLocallyConstantTestRepresentation_tensorProduct
-- name    : GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:14.802293+00:00
-- url     : https://prove2.me/theorems/b7d62649-4bcd-4bee-9bde-02c671885d46
-- title:
--   T: is Locally Constant Test Representation tensor Product
-- statement:
--   The T construction uses the is Locally Constant Test Representation tensor Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProductStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProductStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilProd
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct : ∀ {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y] (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ), IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f → (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by sorry
