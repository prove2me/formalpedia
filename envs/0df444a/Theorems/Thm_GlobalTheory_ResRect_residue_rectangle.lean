-- Prove2me | Theorems.Thm_GlobalTheory_ResRect_residue_rectangle
-- name    : GlobalTheory.ResRect.residue_rectangle
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:19.819143+00:00
-- url     : https://prove2.me/theorems/ad65835a-45f8-434b-8014-fc27ebe8703b
-- title:
--   Res Rect: residue rectangle
-- statement:
--   The Res Rect construction uses the residue rectangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L142-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L142-L215

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ResRect

theorem GlobalTheory.ResRect.residue_rectangle :
    ∀ (f : ℂ → ℂ) (z w : ℂ) (S : Finset ℂ) (r : ℂ → ℂ), z.re < w.re → z.im < w.im → (∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im) → DifferentiableOn ℂ f ((Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im) \ S) → (∀ p ∈ S, ∃ (a : ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g p ∧ ∀ᶠ s in nhdsWithin p {p}ᶜ, f s = a / (s - p) ^ 2 + r p / (s - p) + g s) → (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) + I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) = 2 * Real.pi * I * ∑ p ∈ S, r p := by sorry
