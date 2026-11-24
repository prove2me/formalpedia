-- Prove2me | Theorems.Thm_GlobalTheory_NonUnitShift_linearIndependent_resolvent
-- name    : GlobalTheory.NonUnitShift.linearIndependent_resolvent
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:45.6248+00:00
-- url     : https://prove2.me/theorems/5af602e7-c43f-4fb7-ae19-bde0e96c2446
-- title:
--   Non Unit Shift: linear Independent resolvent
-- statement:
--   The Non Unit Shift construction uses the linear Independent resolvent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearIndependentResolvent.lean#L41-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearIndependentResolvent.lean#L41-L73

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

theorem GlobalTheory.NonUnitShift.linearIndependent_resolvent (T : Module.End ℂ V)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c)) (v : V) (hv : v ≠ 0)
    (w : ℂ → V) (hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v) :
    LinearIndependent ℂ w := by sorry
