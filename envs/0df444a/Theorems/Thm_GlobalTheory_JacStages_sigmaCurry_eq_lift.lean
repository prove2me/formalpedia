-- Prove2me | Theorems.Thm_GlobalTheory_JacStages_sigmaCurry_eq_lift
-- name    : GlobalTheory.JacStages.sigmaCurry_eq_lift
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:39:56.32534+00:00
-- url     : https://prove2.me/theorems/a9da09a4-8ae9-45cb-8f48-49de3f6abe56
-- title:
--   Jac Stages: sigma Curry eq lift
-- statement:
--   The Jac Stages construction uses the sigma Curry eq lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PiExteriorTensorFlattenedIndexEquivNested.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PiExteriorTensorFlattenedIndexEquivNested.lean#L65-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNested
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
noncomputable section
open PiTensorProduct Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.JacStages
variable {α : Type} [DecidableEq α] {β : α → Type} [∀ a, DecidableEq (β a)]
  (M : (Σ a, β a) → Type) [∀ p, AddCommGroup (M p)] [∀ p, Module ℂ (M p)]
variable [Finite α] [∀ a, Finite (β a)]

theorem GlobalTheory.JacStages.sigmaCurry_eq_lift : (sigmaCurry M : (⨂[ℂ] p, M p) →ₗ[ℂ] _) = lift (curryML M) := by sorry
