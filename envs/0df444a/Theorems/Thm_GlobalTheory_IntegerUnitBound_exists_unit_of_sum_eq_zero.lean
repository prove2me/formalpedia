-- Prove2me | Theorems.Thm_GlobalTheory_IntegerUnitBound_exists_unit_of_sum_eq_zero
-- name    : GlobalTheory.IntegerUnitBound.exists_unit_of_sum_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:19:16.092544+00:00
-- url     : https://prove2.me/theorems/cf233715-410b-4ba1-bf5b-31fef95811ef
-- title:
--   Integer Unit Bound: exists unit of sum eq zero
-- statement:
--   The Integer Unit Bound construction uses the exists unit of sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitOfSumEqZero.lean#L32-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitOfSumEqZero.lean#L32-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitOfSumEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open GlobalTheory GlobalTheory.IntegerUnitBound
open scoped Classical

theorem GlobalTheory.IntegerUnitBound.exists_unit_of_sum_eq_zero (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, ∀ t : InfinitePlace E → ℝ, ∑ w, (mult w : ℝ) * t w = 0 → ∃ u : (𝓞 E)ˣ,
      ∀ w : InfinitePlace E, |t w + Real.log (w (u : E))| ≤ C := by sorry
