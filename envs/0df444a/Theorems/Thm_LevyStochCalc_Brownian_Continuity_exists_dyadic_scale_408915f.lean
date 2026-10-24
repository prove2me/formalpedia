-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_exists_dyadic_scale_408915f
-- name    : LevyStochCalc.Brownian.Continuity.exists_dyadic_scale_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:52:04.38714+00:00
-- url     : https://prove2.me/theorems/4ec8177d-188a-456b-988f-36033e30244d
-- title:
--   Dyadic Scale Selection
-- statement:
--   This is a deterministic dyadic-scale selection lemma. For a real number $d$ satisfying $0<d\le 1$, there exists $m\in\mathbb N$ such that
--
--   $$
--   (1/2)^{m+1}<d\le (1/2)^m.
--   $$
--
--   The result provides the discrete scale used to compare an arbitrary distance with dyadic levels in chaining arguments.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L339-L355 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.exists_dyadic_scale`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Continuity.exists_dyadic_scale_408915f {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∃ m : ℕ, (1 / 2 : ℝ) ^ (m + 1) < d ∧ d ≤ (1 / 2) ^ m := by sorry
