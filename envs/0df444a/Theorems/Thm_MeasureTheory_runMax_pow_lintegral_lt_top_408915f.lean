-- Prove2me | Theorems.Thm_MeasureTheory_runMax_pow_lintegral_lt_top_408915f
-- name    : MeasureTheory.runMax_pow_lintegral_lt_top_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:59:11.292372+00:00
-- url     : https://prove2.me/theorems/16508c28-0f0d-454f-aa18-805dda92d4c4
-- title:
--   Finiteness of the Maximal $L^p$ Integral
-- statement:
--   This private auxiliary lemma transfers finiteness from a submartingale terminal value to its running maximum.
--
--   Let $f$ be a nonnegative submartingale under a finite measure, let $p>1$, and fix $n\in\mathbb N$. If
--
--   $$
--   \int f_n^p\,d\mu<\infty,
--   $$
--
--   then
--
--   $$
--   \int (f_n^\ast)^p\,d\mu<\infty,
--   $$
--
--   where $f_n^\ast$ is the maximum of $f_k$ for $k\leq n$. The integrals are `ENNReal` lower integrals of `ENNReal.ofReal` powers.
--
--   This result supplies the finiteness needed to pass from truncated maximal estimates to the untruncated setting.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L841-L925 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.runMax_pow_lintegral_lt_top`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma MeasureTheory.runMax_pow_lintegral_lt_top_408915f
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω) (hp : 1 < p) (n : ℕ)
    (hB_lt_top : ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ < ⊤) :
    ∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ < ⊤ := by sorry
