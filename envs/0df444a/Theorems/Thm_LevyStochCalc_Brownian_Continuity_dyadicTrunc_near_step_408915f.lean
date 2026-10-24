-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadicTrunc_near_step_408915f
-- name    : LevyStochCalc.Brownian.Continuity.dyadicTrunc_near_step_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:51:58.636619+00:00
-- url     : https://prove2.me/theorems/453d0f6e-52b3-48a6-8c5c-1bf2cb1c4c10
-- title:
--   Dyadic Truncation Bound at One Scale
-- statement:
--   Let f : ℝ → ℝ, b : ℕ → ℝ with b(n) ≥ 0, and N : ℕ. Suppose that for every n ≥ N and every integer k with 0 ≤ k and k+1 ≤ 2ⁿ,
--
--   $$\left|f\!\left(\frac{k+1}{2^n}\right)-f\!\left(\frac{k}{2^n}\right)\right|\le b(n).$$
--
--   Then for m ≥ N and 0 ≤ s ≤ t ≤ 1 with t−s ≤ (1/2)^m,
--
--   $$|f(\operatorname{dyadicTrunc}(m,s))-f(\operatorname{dyadicTrunc}(m,t))|\le b(m).$$
--
--   This is the cross-point estimate that connects nearby points at a common dyadic scale.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L270-L308 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.dyadicTrunc_near_step`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Continuity.dyadicTrunc_near_step_408915f {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {m : ℕ} (hm : N ≤ m) {s t : ℝ} (hs0 : 0 ≤ s) (ht1 : t ≤ 1) (hst : s ≤ t)
    (hclose : t - s ≤ (1 / 2) ^ m) :
    |f (dyadicTrunc m s) - f (dyadicTrunc m t)| ≤ b m := by sorry
