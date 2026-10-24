-- Prove2me | Theorems.Thm_MeasureTheory_maximal_ineq_Lp_408915f
-- name    : MeasureTheory.maximal_ineq_Lp_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:01:59.604011+00:00
-- url     : https://prove2.me/theorems/33426b0d-6ddc-4199-ae85-d31e8878c84f
-- title:
--   Doob’s Discrete-Time $L^p$ Maximal Inequality
-- statement:
--   This formalizes Doob’s strong-type maximal inequality for discrete-time submartingales.
--
--   Let $(\Omega,\mathcal F,\mu)$ be a finite measure space, let $\mathcal G$ be a filtration indexed by $\mathbb N$, let $f_n:\Omega\to\mathbb R$ be a $\mathcal G$-submartingale, and let $p\in\mathbb R$ satisfy $1<p$. Assume $f_n(\omega)\ge 0$ for every $n$ and $\omega$. For each $n$, define the running maximum $f_n^*(\omega)=\max_{0\le k\le n}f_k(\omega)$.
--
--   $$\|f_n^*\|_{L^p(\mu)}\le \frac{p}{p-1}\,\|f_n\|_{L^p(\mu)}.$$
--
--   The Lean statement uses `eLpNorm` with exponent `ENNReal.ofReal p`; thus both sides are values in $[0,\infty]$, and the running maximum is represented by a finite supremum. This is a reusable strong-type maximal estimate.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L927-L984 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `MeasureTheory.maximal_ineq_Lp`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem MeasureTheory.maximal_ineq_Lp_408915f
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ f k ω)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) *
          eLpNorm (f n) (ENNReal.ofReal p) μ := by sorry
