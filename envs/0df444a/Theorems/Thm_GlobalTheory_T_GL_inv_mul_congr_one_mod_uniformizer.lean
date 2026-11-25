-- Prove2me | Theorems.Thm_GlobalTheory_T_GL_inv_mul_congr_one_mod_uniformizer
-- name    : GlobalTheory.T.GL_inv_mul_congr_one_mod_uniformizer
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:36.324326+00:00
-- url     : https://prove2.me/theorems/fcb6cb90-98de-5cfb-82e0-ad8ff702268e
-- title:
--   T: GL inv mul congr one mod uniformizer
-- statement:
--   The T construction uses the GL inv mul congr one mod uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/GLInvMulCongrOneModUniformizerStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/GLInvMulCongrOneModUniformizerStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GLInvMulCongrOneModUniformizer
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GLInvMulCongrOneModUniformizerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.GL_inv_mul_congr_one_mod_uniformizer : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {N : ℕ} (π : K), π ≠ 0 → Valued.v π < 1 →
  ∀ (a a₁ : GL (Fin N) K), (∀ i j, Valued.v (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    (∀ i j, Valued.v (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    ∀ i j, Valued.v (π⁻¹ * (((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1 := by sorry
