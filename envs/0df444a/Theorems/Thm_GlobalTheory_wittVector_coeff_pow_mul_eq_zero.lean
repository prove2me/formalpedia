-- Prove2me | Theorems.Thm_GlobalTheory_wittVector_coeff_pow_mul_eq_zero
-- name    : GlobalTheory.wittVector_coeff_pow_mul_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:13.617834+00:00
-- url     : https://prove2.me/theorems/dd8c8eab-10e2-4249-bd82-f4e0be8c5b5b
-- title:
--   Global Theory: witt Vector coeff pow mul eq zero
-- statement:
--   The Global Theory construction uses the witt Vector coeff pow mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorDvdOfSaturatedIdeal.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorDvdOfSaturatedIdeal.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorDvdOfSaturatedIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WittVector

theorem GlobalTheory.wittVector_coeff_pow_mul_eq_zero {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] : ∀ (m : ℕ) (t : WittVector l R) (j : ℕ), j < m →
      ((l : WittVector l R) ^ m * t).coeff j = 0 := by sorry
