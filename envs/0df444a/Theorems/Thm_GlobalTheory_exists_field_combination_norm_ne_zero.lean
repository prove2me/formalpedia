-- Prove2me | Theorems.Thm_GlobalTheory_exists_field_combination_norm_ne_zero
-- name    : GlobalTheory.exists_field_combination_norm_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:19.858441+00:00
-- url     : https://prove2.me/theorems/2affd81e-7401-43ed-8600-66d47b730bd3
-- title:
--   Global Theory: exists field combination norm ne zero
-- statement:
--   The Global Theory construction uses the exists field combination norm ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFieldCombinationNormNeZero.lean#L8-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFieldCombinationNormNeZero.lean#L8-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsFieldCombinationNormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.exists_field_combination_norm_ne_zero {k B A : Type} [Field k] [Infinite k] [CommRing B]
    [IsDomain B] [Algebra k B] [CommRing A] [Algebra B A] [Module.Free B A] [Module.Finite B A]
    {d : ℕ} (y : Fin d → A) (hx : ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0) :
    ∃ a : Fin d → k, Algebra.norm B (∑ i, algebraMap k B (a i) • y i) ≠ 0 := by sorry
