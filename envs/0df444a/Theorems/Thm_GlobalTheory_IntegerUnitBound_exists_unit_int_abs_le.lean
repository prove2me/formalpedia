-- Prove2me | Theorems.Thm_GlobalTheory_IntegerUnitBound_exists_unit_int_abs_le
-- name    : GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:28.155033+00:00
-- url     : https://prove2.me/theorems/f4d5d21b-1985-4f92-ba48-0de9391d141b
-- title:
--   Integer Unit Bound: exists unit int abs le
-- statement:
--   The Integer Unit Bound construction uses the exists unit int abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitOfSumEqZero.lean#L76-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitOfSumEqZero.lean#L76-L105

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

theorem GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (n : ℤ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + (n : ℝ)| ≤ R := by sorry
