-- Prove2me | Theorems.Thm_MeasureTheory_fubini_swap_truncated_408915f
-- name    : MeasureTheory.fubini_swap_truncated_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:59:13.068932+00:00
-- url     : https://prove2.me/theorems/45716c15-d6df-4ca7-a076-e0ed11398324
-- title:
--   Truncated Fubini Swap
-- statement:
--   This private auxiliary lemma is the truncated analogue of the maximal layer-integral Fubini identity.
--
--   Let $f$ be a nonnegative submartingale, let $p>1$, fix $n\in\mathbb N$, and let $K>0$. Then
--
--   $$
--   \int_{(0,K]}t^{p-2}\int_{\{\,\omega:t\leq f_n^\ast(\omega)\}}f_n(\omega)\,d\mu\,dt
--   =
--   \int_\Omega f_n(\omega)
--   \frac{\min(f_n^\ast(\omega),K)^{p-1}}{p-1}\,d\mu.
--   $$
--
--   This technical identity prepares the truncated Hölder estimate.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L426-L562 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.fubini_swap_truncated`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Martingale.OptionalStopping

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal
section
namespace MeasureTheory
end MeasureTheory
open MeasureTheory
variable {Ω : Type*}
variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}

lemma MeasureTheory.fubini_swap_truncated_408915f
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    ∫⁻ t in Set.Ioc (0:ℝ) K,
        ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1) / (p - 1)) ∂μ := by sorry
