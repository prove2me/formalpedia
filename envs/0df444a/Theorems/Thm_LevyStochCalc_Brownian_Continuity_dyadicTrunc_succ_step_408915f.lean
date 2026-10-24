-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadicTrunc_succ_step_408915f
-- name    : LevyStochCalc.Brownian.Continuity.dyadicTrunc_succ_step_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:51:59.486996+00:00
-- url     : https://prove2.me/theorems/8b316446-2f14-4100-8456-58840d14b829
-- title:
--   Successive Dyadic Truncation Step
-- statement:
--   Let f and b satisfy the nonnegative level bounds from `dyadicTrunc_near_step`: for every n ≥ N and every admissible integer k, consecutive level-n dyadics have f-increment at most b(n). If n+1 ≥ N and 0 ≤ x ≤ 1, then
--
--   $$|f(\operatorname{dyadicTrunc}(n+1,x))-f(\operatorname{dyadicTrunc}(n,x))|\le b(n+1).$$
--
--   The lemma `dyadicTrunc_succ_step` controls one refinement of the dyadic approximation.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L209-L243 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.dyadicTrunc_succ_step`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Continuity.dyadicTrunc_succ_step_408915f {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {n : ℕ} (hn : N ≤ n + 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |f (dyadicTrunc (n + 1) x) - f (dyadicTrunc n x)| ≤ b (n + 1) := by sorry
