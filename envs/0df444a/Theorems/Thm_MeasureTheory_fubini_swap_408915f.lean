-- Prove2me | Theorems.Thm_MeasureTheory_fubini_swap_408915f
-- name    : MeasureTheory.fubini_swap_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:59:16.737299+00:00
-- url     : https://prove2.me/theorems/f0653450-15f6-4c39-93be-2a85e50fca8d
-- title:
--   Fubini Swap for the Maximal Layer Integral
-- statement:
--   This private auxiliary lemma performs the Fubini step for a nonnegative submartingale.
--
--   Let $f:\mathbb N\times\Omega\to\mathbb R$ be a nonnegative submartingale with respect to a filtration $\mathcal G$ and a finite measure $\mu$, let $p>1$, and fix $n\in\mathbb N$. Then
--
--   $$
--   \int_{(0,\infty)} t^{p-2}\int_{\{\,\omega:t\leq f_n^\ast(\omega)\}}f_n(\omega)\,d\mu\,dt
--   =
--   \int_\Omega f_n(\omega)\frac{(f_n^\ast(\omega))^{p-1}}{p-1}\,d\mu,
--   $$
--
--   where $f_n^\ast$ is the discrete running maximum.
--
--   This is a technical Fubini identity used in the strong Doob $L^p$ estimate.
--
--   **Formalization Note.** The displayed integrals are represented as `ENNReal` lower integrals with `ofReal` coercions.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L189-L339 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.fubini_swap`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma MeasureTheory.fubini_swap_408915f
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1) / (p - 1)) ∂μ := by sorry
