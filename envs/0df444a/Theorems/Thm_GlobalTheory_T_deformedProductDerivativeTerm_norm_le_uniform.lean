-- Prove2me | Theorems.Thm_GlobalTheory_T_deformedProductDerivativeTerm_norm_le_uniform
-- name    : GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:32:00.726709+00:00
-- url     : https://prove2.me/theorems/ddebb72b-7224-46ac-bde8-202120f70637
-- title:
--   T: deformed Product Derivative Term norm le uniform
-- statement:
--   The T construction uses the deformed Product Derivative Term norm le uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DeformedProductDerivativeTermNormLeUniformStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DeformedProductDerivativeTermNormLeUniformStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniform
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniformStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (m : I → ℕ) (r : ℝ), r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 → ‖dTerm φ (2 * s) m z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) := by sorry
