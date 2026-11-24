-- Prove2me | Theorems.Thm_GlobalTheory_IntegralPointNormSquareBound_exists_pos_mul_norm_sq_le
-- name    : GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:05.593677+00:00
-- url     : https://prove2.me/theorems/67dd3bdb-a2e8-4ba6-bf10-43c3e345e1a4
-- title:
--   Integral Point Norm Square Bound: exists pos mul norm sq le
-- statement:
--   The Integral Point Norm Square Bound construction uses the exists pos mul norm sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsPosMulNormSqLe.lean#L5-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsPosMulNormSqLe.lean#L5-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralPointNormSquareBound

theorem GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (h : ∀ v : V, v ≠ 0 → 0 < om v (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖ ^ 2 ≤ om v (J v) := by sorry
