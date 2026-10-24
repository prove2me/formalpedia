-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadic_holder_chaining_408915f
-- name    : LevyStochCalc.Brownian.Continuity.dyadic_holder_chaining_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:51:58.959873+00:00
-- url     : https://prove2.me/theorems/eb94f523-b5e7-4d03-9ec9-9edc1cc353b9
-- title:
--   Deterministic Dyadic Hölder Chaining
-- statement:
--   This is the deterministic dyadic Hölder-chaining lemma. Let $f:\mathbb R\to\mathbb R$, $\alpha,C\in\mathbb R$, and $N\in\mathbb N$, with $\alpha>0$ and $C\ge0$. Assume that for every $n\ge N$, every integer $k$ with $0\le k$ and $k+1\le2^n$, the consecutive dyadic increment satisfies
--
--   $$
--   \left|f\!\left(\frac{k+1}{2^n}\right)-f\!\left(\frac{k}{2^n}\right)\right|
--   \le C\bigl((1/2)^\alpha\bigr)^n.
--   $$
--
--   Then there exists $K\ge0$ such that for all dyadic rationals $s,t\in[0,1]$ with $|s-t|\le(1/2)^N$,
--
--   $$
--   |f(s)-f(t)|\le K|s-t|^\alpha.
--   $$
--
--   This supplies the deterministic pathwise estimate used after obtaining eventual dyadic increment bounds.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L402-L519 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.dyadic_holder_chaining`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Continuity

lemma LevyStochCalc.Brownian.Continuity.dyadic_holder_chaining_408915f {f : ℝ → ℝ} {α C : ℝ} {N : ℕ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ C * ((1 / 2 : ℝ) ^ α) ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
      0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → |s - t| ≤ (1 / 2 : ℝ) ^ N →
      |f s - f t| ≤ K * |s - t| ^ α := by sorry
