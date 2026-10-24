-- Prove2me | Theorems.Thm_MeasureTheory_A_K_le_layer_integral_408915f
-- name    : MeasureTheory.A_K_le_layer_integral_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:59:19.846983+00:00
-- url     : https://prove2.me/theorems/e323aebb-6569-44d6-a81c-dea717b27d84
-- title:
--   Truncated Layer-Cake Bound
-- statement:
--   This private auxiliary lemma bounds the truncated maximal moment.
--
--   Let $f$ be a nonnegative submartingale, let $p>1$, fix $n\in\mathbb N$, and let $K>0$. Writing $f_n^\ast$ for the running maximum, one has
--
--   $$
--   \int \big(\min(f_n^\ast,K)\big)^p\,d\mu
--   \leq
--   p\int_{(0,K]}t^{p-2}
--   \left(\int_{\{\omega:t\leq f_n^\ast(\omega)\}}f_n(\omega)\,d\mu\right)dt.
--   $$
--
--   The quantities are represented using `ENNReal.ofReal` and lower integrals.
--
--   This is the truncated layer-cake stage of the proof of the strong Doob inequality.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L564-L649 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.A_K_le_layer_integral`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma MeasureTheory.A_K_le_layer_integral_408915f
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    ∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) ∂μ
      ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioc (0:ℝ) K,
            ENNReal.ofReal (t ^ (p - 2)) *
              ENNReal.ofReal (∫ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, f n ω ∂μ) := by sorry
