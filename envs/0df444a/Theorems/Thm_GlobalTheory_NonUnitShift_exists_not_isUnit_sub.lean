-- Prove2me | Theorems.Thm_GlobalTheory_NonUnitShift_exists_not_isUnit_sub
-- name    : GlobalTheory.NonUnitShift.exists_not_isUnit_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:55.967252+00:00
-- url     : https://prove2.me/theorems/0fa254d6-67e7-4633-a7ad-22439a92023c
-- title:
--   Non Unit Shift: exists not is Unit sub
-- statement:
--   The Non Unit Shift construction uses the exists not is Unit sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearIndependentResolvent.lean#L75-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearIndependentResolvent.lean#L75-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentResolvent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonUnitShift
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.NonUnitShift.exists_not_isUnit_sub : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V] [Nontrivial V], Module.rank ℂ V ≤ Cardinal.aleph0 → ∀ (T : Module.End ℂ V), ∃ (c : ℂ), ¬IsUnit (T - (Algebra.algebraMap ℂ (Module.End ℂ V) : ℂ → Module.End ℂ V) c) := by sorry
