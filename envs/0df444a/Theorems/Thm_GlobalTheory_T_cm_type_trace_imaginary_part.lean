-- Prove2me | Theorems.Thm_GlobalTheory_T_cm_type_trace_imaginary_part
-- name    : GlobalTheory.T.cm_type_trace_imaginary_part
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:01.524585+00:00
-- url     : https://prove2.me/theorems/b1e9c8e0-64d6-4b9a-9728-a8a08d642a84
-- title:
--   T: cm type trace imaginary part
-- statement:
--   The T construction uses the cm type trace imaginary part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypeTraceImaginaryPartStatement.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypeTraceImaginaryPartStatement.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeTraceImaginaryPart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeTraceImaginaryPartStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.CMVal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cm_type_trace_imaginary_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (h : I → ℝ) (mu : E), (∀ z : E, ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) = ∑ i, h i * (φ i z).im) →
    ∀ i, 2 * Complex.I * φ i mu = (h i : ℂ) := by sorry
