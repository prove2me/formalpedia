-- Prove2me | Theorems.Thm_GlobalTheory_powerSeries_eq_C_of_subst_eq_self
-- name    : GlobalTheory.powerSeries_eq_C_of_subst_eq_self
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:55:52.259456+00:00
-- url     : https://prove2.me/theorems/617006f3-f69f-44c3-83f2-3b8cb929c079
-- title:
--   Global Theory: power Series eq C of subst eq self
-- statement:
--   The Global Theory construction uses the power Series eq C of subst eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowerSeriesEqCOfSubstFixedNotRootOfUnity.lean#L7-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowerSeriesEqCOfSubstFixedNotRootOfUnity.lean#L7-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowerSeriesEqCOfSubstFixedNotRootOfUnity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open PowerSeries

theorem GlobalTheory.powerSeries_eq_C_of_subst_eq_self (L : Type) [Field L] (y : PowerSeries L)
    (hy : PowerSeries.constantCoeff y = 0)
    (hu : ∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) (a : PowerSeries L)
    (ha : (PowerSeries.subst y a : PowerSeries L) = a) :
    a = PowerSeries.C (PowerSeries.constantCoeff a) := by sorry
