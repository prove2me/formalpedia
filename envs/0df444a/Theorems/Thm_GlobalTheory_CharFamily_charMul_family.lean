-- Prove2me | Theorems.Thm_GlobalTheory_CharFamily_charMul_family
-- name    : GlobalTheory.CharFamily.charMul_family
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:59.343981+00:00
-- url     : https://prove2.me/theorems/cdfb0996-d84a-41f1-a771-edcabb99773d
-- title:
--   Char Family: char Mul family
-- statement:
--   The Char Family construction uses the char Mul family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFamilyPhaseBound.lean#L123-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFamilyPhaseBound.lean#L123-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
open GlobalTheory GlobalTheory.CharFamily
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem GlobalTheory.CharFamily.charMul_family : ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P →L[ℝ] E →L[ℝ] ℝ) (f : SchwartzMap E ℂ), ∃ Φ : P → SchwartzMap E ℂ,
    (∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x) ∧ Continuous Φ ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n) := by sorry
