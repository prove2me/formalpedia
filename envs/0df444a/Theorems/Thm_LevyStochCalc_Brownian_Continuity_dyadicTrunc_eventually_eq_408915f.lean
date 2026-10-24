-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadicTrunc_eventually_eq_408915f
-- name    : LevyStochCalc.Brownian.Continuity.dyadicTrunc_eventually_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:52:01.531511+00:00
-- url     : https://prove2.me/theorems/6db901f2-8e01-4352-8b2a-156317709f77
-- title:
--   Eventual Stability of Dyadic Truncation
-- statement:
--   If s is a dyadic rational, then there exists L₀ : ℕ such that for every L ≥ L₀, its level-L dyadic truncation equals s:
--
--   $$s\in\operatorname{dyadicRationals}\Longrightarrow\exists L_0\,\forall L\ge L_0,\ \operatorname{dyadicTrunc}(L,s)=s.$$
--
--   The lemma `dyadicTrunc_eventually_eq` records eventual exactness of truncation on the dense dyadic set.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L310-L325 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.dyadicTrunc_eventually_eq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Continuity.dyadicTrunc_eventually_eq_408915f {s : ℝ} (hs : s ∈ dyadicRationals) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → dyadicTrunc L s = s := by sorry
