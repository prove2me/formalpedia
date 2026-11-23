-- Prove2me | Theorems.Thm_GlobalTheory_CommTriang_blockOne_succ_zero
-- name    : GlobalTheory.CommTriang.blockOne_succ_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:37.014912+00:00
-- url     : https://prove2.me/theorems/4f1914d3-75e5-47c1-b8c6-61aaa66983ec
-- title:
--   Comm Triang: block One succ zero
-- statement:
--   The Comm Triang construction uses the block One succ zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonEigenvectorCommuting.lean#L98-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonEigenvectorCommuting.lean#L98-L98

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
variable {k : Type} [Field k] {n : ℕ}

theorem GlobalTheory.CommTriang.blockOne_succ_zero (Q : Matrix (Fin n) (Fin n) k) (a : Fin n) : blockOne Q a.succ 0 = 0 := by sorry

attribute [defeq] GlobalTheory.CommTriang.blockOne_succ_zero
