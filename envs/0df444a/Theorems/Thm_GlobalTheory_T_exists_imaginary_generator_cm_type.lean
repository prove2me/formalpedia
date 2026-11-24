-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_imaginary_generator_cm_type
-- name    : GlobalTheory.T.exists_imaginary_generator_cm_type
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:48.118724+00:00
-- url     : https://prove2.me/theorems/fe8a036e-56a6-4791-bdc0-4843eece1c46
-- title:
--   T: exists imaginary generator cm type
-- statement:
--   The T construction uses the exists imaginary generator cm type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsImaginaryGeneratorCmTypeStatement.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsImaginaryGeneratorCmTypeStatement.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImaginaryGeneratorCmType
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImaginaryGeneratorCmTypeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_imaginary_generator_cm_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E), IsUnit M →
    (∀ ξ ∈ M, IsCMField.complexConj E ξ = -ξ) → ∀ (I : Type) (φ : I → E →+* ℂ), IsCMType φ → ∀ (e₀ : ℤˣ) (l : ℕ), l.Prime →
    ∃ ξ ∈ M, (∀ i, 0 < ((e₀ : ℤ) : ℝ) * (φ i ξ).im) ∧
      ∀ η ∈ M, ∃ n : ℕ, n.Coprime l ∧ ∃ a : OF E, (n : E) * η = algebraMap (OF E) E a * ξ := by sorry
