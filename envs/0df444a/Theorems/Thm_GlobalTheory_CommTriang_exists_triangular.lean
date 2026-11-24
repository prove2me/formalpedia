-- Prove2me | Theorems.Thm_GlobalTheory_CommTriang_exists_triangular
-- name    : GlobalTheory.CommTriang.exists_triangular
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:58:58.0876+00:00
-- url     : https://prove2.me/theorems/ef0f4512-f455-488c-bc87-0177c97c8ca1
-- title:
--   Comm Triang: exists triangular
-- statement:
--   The Comm Triang construction uses the exists triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonEigenvectorCommuting.lean#L135-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonEigenvectorCommuting.lean#L135-L235

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisFurther
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonEigenvectorCommuting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CommTriang
open Matrix

theorem GlobalTheory.CommTriang.exists_triangular (k ι : Type) [Field k] [IsAlgClosed k] : ∀ (n : ℕ) (T : ι → Matrix (Fin n) (Fin n) k),
    (∀ i j, T i * T j = T j * T i) →
    ∃ P : Matrix (Fin n) (Fin n) k, IsUnit P ∧ (∀ i, (P⁻¹ * T i * P).BlockTriangular id) ∧
      ∀ a, ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, (T i).mulVec x = (P⁻¹ * T i * P) a a • x := by sorry
