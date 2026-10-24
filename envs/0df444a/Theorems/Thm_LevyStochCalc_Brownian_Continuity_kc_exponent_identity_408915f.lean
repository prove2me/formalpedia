-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_exponent_identity_408915f
-- name    : LevyStochCalc.Brownian.Continuity.kc_exponent_identity_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:51:58.06866+00:00
-- url     : https://prove2.me/theorems/dd045e01-7866-4eca-9ebc-b78b4562a392
-- title:
--   Kolmogorov–Chentsov Exponent Identity
-- statement:
--   This is an algebraic identity for the per-level Kolmogorov–Chentsov factor. For $\alpha,p,q\in\mathbb R$ and $n\in\mathbb N$,
--
--   $$
--   \frac{2^n\bigl((1/2)^n\bigr)^q}{\bigl(((1/2)^\alpha)^n\bigr)^p}
--   =\bigl((1/2)^{q-\alpha p-1}\bigr)^n.
--   $$
--
--   It isolates the geometric ratio governing summability of dyadic-level estimates.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L377-L400 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.kc_exponent_identity`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Continuity.kc_exponent_identity_408915f {α p q : ℝ} (n : ℕ) :
    (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p
      = ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n := by sorry
