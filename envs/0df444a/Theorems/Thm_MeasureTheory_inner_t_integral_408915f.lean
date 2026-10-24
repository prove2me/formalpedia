-- Prove2me | Theorems.Thm_MeasureTheory_inner_t_integral_408915f
-- name    : MeasureTheory.inner_t_integral_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:59:12.495442+00:00
-- url     : https://prove2.me/theorems/ef8e1eba-f781-4699-82c1-df97f7472d1c
-- title:
--   Layer-Cake Inner Integral Evaluation
-- statement:
--   This private auxiliary lemma evaluates a pointwise extended-real integral.
--
--   Let $f_\ast\geq0$ and $p>1$. Then
--
--   $$
--   \int_{(0,\infty)} t^{p-2}\,\mathbf 1_{\{t\leq f_\ast\}}\,dt
--   =
--   \frac{f_\ast^{p-1}}{p-1},
--   $$
--
--   with both sides interpreted through `ENNReal.ofReal`.
--
--   The identity is the scalar integration step in the layer-cake proof of Doob's $L^p$ maximal inequality.
--
--   **Formalization Note.** The integral is an `ENNReal` lower integral over $(0,\infty)$, and the indicator is $\mathbf 1_{\{t\leq f_\ast\}}$.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L140-L187 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.inner_t_integral`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma MeasureTheory.inner_t_integral_408915f
    {fstar p : ℝ} (hfstar : 0 ≤ fstar) (hp : 1 < p) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t
      = ENNReal.ofReal (fstar ^ (p - 1) / (p - 1)) := by sorry
