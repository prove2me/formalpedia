-- Prove2me | Theorems.Thm_MeasureTheory_holder_step_408915f
-- name    : MeasureTheory.holder_step_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:59:14.133336+00:00
-- url     : https://prove2.me/theorems/33900796-d33e-4c4f-8857-bcebf1ce548d
-- title:
--   Hölder Bound for the Maximal Integral
-- statement:
--   This private auxiliary lemma gives the main algebraic estimate in the untruncated Doob argument.
--
--   Let $f$ be a nonnegative submartingale under a finite measure, let $p>1$, and fix $n\in\mathbb N$. Then
--
--   $$
--   \int f_n^{\ast p}\,d\mu
--   \leq
--   \frac{p}{p-1}
--   \left(\int f_n^p\,d\mu\right)^{1/p}
--   \left(\int f_n^{\ast p}\,d\mu\right)^{(p-1)/p},
--   $$
--
--   with all integrals interpreted as `ENNReal` integrals of `ENNReal.ofReal` powers.
--
--   The statement is a technical intermediate estimate rather than the final maximal inequality.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L755-L820 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.holder_step`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma MeasureTheory.holder_step_408915f
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ)
      ≤ ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ) ^ ((p - 1) / p) := by sorry
