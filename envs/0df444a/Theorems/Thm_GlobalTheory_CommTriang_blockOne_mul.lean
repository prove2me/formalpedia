-- Prove2me | Theorems.Thm_GlobalTheory_CommTriang_blockOne_mul
-- name    : GlobalTheory.CommTriang.blockOne_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:15:05.693824+00:00
-- url     : https://prove2.me/theorems/8de3b1dd-841c-4491-96e3-f5f1c2bf5fd4
-- title:
--   Comm Triang: block One mul
-- statement:
--   The Comm Triang construction uses the block One mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonEigenvectorCommuting.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonEigenvectorCommuting.lean#L101-L103

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

theorem GlobalTheory.CommTriang.blockOne_mul (Q R : Matrix (Fin n) (Fin n) k) : blockOne Q * blockOne R = blockOne (Q * R) := by sorry
