-- Prove2me | Theorems.Thm_GlobalTheory_CommTriang_conj_succ_zero
-- name    : GlobalTheory.CommTriang.conj_succ_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:15:01.697485+00:00
-- url     : https://prove2.me/theorems/168fe342-13d3-40a4-91f8-ac0f5c100f21
-- title:
--   Comm Triang: conj succ zero
-- statement:
--   The Comm Triang construction uses the conj succ zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonEigenvectorCommuting.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonEigenvectorCommuting.lean#L113-L115

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

theorem GlobalTheory.CommTriang.conj_succ_zero (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) (a : Fin n) :
    (blockOne R * S * blockOne Q) a.succ 0 = ∑ c, R a c * S c.succ 0 := by sorry
