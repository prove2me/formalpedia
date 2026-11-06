-- Prove2me | Theorems.Thm_OAI_SevenEighths_Continuation_nonzero_of_regularized_signal
-- name    : OAI.SevenEighths.Continuation.nonzero_of_regularized_signal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:16.550416+00:00
-- url     : https://prove2.me/theorems/e4dd466d-1456-47bf-b24f-4f8f30e91476
-- title:
--   Continuation: nonzero of regularized signal
-- statement:
--   The Continuation construction uses the nonzero of regularized signal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Continuation.lean#L92-L111
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Continuation.lean#L92-L111

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.Continuation

theorem OAI.SevenEighths.Continuation.nonzero_of_regularized_signal (a b c : ℝ)
    (L Lregular R W : ℂ → ℂ) (f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular {s : ℂ | a < s.re})
    (hR : AnalyticOnNhd ℂ R {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f)
    (heq : ∀ s : ℂ, max a b < s.re →
      Lregular s * signalMellin f c s = R s * W s)
    {ρ : ℂ} (hρ : a < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ)
    (hRρ : R ρ ≠ 0) (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by sorry
