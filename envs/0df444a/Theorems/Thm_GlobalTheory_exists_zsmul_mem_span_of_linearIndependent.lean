-- Prove2me | Theorems.Thm_GlobalTheory_exists_zsmul_mem_span_of_linearIndependent
-- name    : GlobalTheory.exists_zsmul_mem_span_of_linearIndependent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:20.968105+00:00
-- url     : https://prove2.me/theorems/c5033383-88d5-4def-84c3-29e1069ea857
-- title:
--   Global Theory: exists zsmul mem span of linear Independent
-- statement:
--   The Global Theory construction uses the exists zsmul mem span of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L212-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L212-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric

theorem GlobalTheory.exists_zsmul_mem_span_of_linearIndependent {A : Type*} [AddCommGroup A]
    [Module.Finite ℤ A] {n : ℕ} (hn : finrank ℤ A = n) {v : Fin n → A}
    (hv : LinearIndependent ℤ v) (x : A) :
    ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ Submodule.span ℤ (Set.range v) := by sorry
