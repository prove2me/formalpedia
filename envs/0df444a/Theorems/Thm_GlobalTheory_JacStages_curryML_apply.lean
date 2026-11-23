-- Prove2me | Theorems.Thm_GlobalTheory_JacStages_curryML_apply
-- name    : GlobalTheory.JacStages.curryML_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:56.096834+00:00
-- url     : https://prove2.me/theorems/ca47730d-0562-4cb3-b182-188862f53f10
-- title:
--   Jac Stages: curry ML apply
-- statement:
--   The Jac Stages construction uses the curry ML apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PiExteriorTensorFlattenedIndexEquivNested.lean#L52-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PiExteriorTensorFlattenedIndexEquivNested.lean#L52-L52

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

theorem GlobalTheory.JacStages.curryML_apply (x : ∀ p, M p) : curryML M x = tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by sorry
