-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_root_additive_poly_eq_of_unit_coeff
-- name    : GlobalTheory.T.exists_root_additive_poly_eq_of_unit_coeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:38:53.409843+00:00
-- url     : https://prove2.me/theorems/94ecb1be-5784-4bc8-8c33-816cd76223e4
-- title:
--   T: exists root additive poly eq of unit coeff
-- statement:
--   The T construction uses the exists root additive poly eq of unit coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OntoOCAdditivePolyStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OntoOCAdditivePolyStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OntoOCAdditivePoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OntoOCAdditivePolyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_root_additive_poly_eq_of_unit_coeff : ∀ (l : ℕ) [Fact l.Prime] (E N : ℕ) (a : ℕ → ℂ_[l]), N ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a N‖ = 1 → ∀ b : ℂ_[l], ‖b‖ ≤ 1 → ∃ W : ℂ_[l], ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = b := by sorry
