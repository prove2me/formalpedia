-- Prove2me | Theorems.Thm_GlobalTheory_CharMult_multiplier_symm
-- name    : GlobalTheory.CharMult.multiplier_symm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:08:02.213805+00:00
-- url     : https://prove2.me/theorems/c676f412-cd05-4c16-9b19-27ce3bcd96a7
-- title:
--   Char Mult: multiplier symm
-- statement:
--   The Char Mult construction uses the multiplier symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslationCharacterInvariantForm.lean#L11-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslationCharacterInvariantForm.lean#L11-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperpositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFourierRepresentationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzInnerProductContinuousStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationCharacterInvariantForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CharMult

theorem GlobalTheory.CharMult.multiplier_symm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' g g' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) →
      (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    ∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x)) := by sorry
