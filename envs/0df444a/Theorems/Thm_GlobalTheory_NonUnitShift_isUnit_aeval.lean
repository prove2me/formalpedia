-- Prove2me | Theorems.Thm_GlobalTheory_NonUnitShift_isUnit_aeval
-- name    : GlobalTheory.NonUnitShift.isUnit_aeval
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:29.351635+00:00
-- url     : https://prove2.me/theorems/d365c1bc-750e-4d97-bd6c-136f5012dd3b
-- title:
--   Non Unit Shift: is Unit aeval
-- statement:
--   The Non Unit Shift construction uses the is Unit aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearIndependentResolvent.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearIndependentResolvent.lean#L9-L39

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

theorem GlobalTheory.NonUnitShift.isUnit_aeval (T : Module.End ℂ V)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c)) :
    ∀ (n : ℕ) (p : ℂ[X]), p.natDegree = n → p ≠ 0 → IsUnit (aeval T p) := by sorry
