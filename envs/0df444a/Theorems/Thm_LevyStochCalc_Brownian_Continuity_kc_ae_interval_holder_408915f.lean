-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_ae_interval_holder_408915f
-- name    : LevyStochCalc.Brownian.Continuity.kc_ae_interval_holder_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:52:01.595154+00:00
-- url     : https://prove2.me/theorems/b9a878cf-1146-4f85-9a60-a48a4d7cc66c
-- title:
--   Almost-Sure Local Hölder Bounds on Unit Intervals
-- statement:
--   This is the almost-sure intervalwise Hölder estimate for a Kolmogorov process. Under the probability-space, process, and `IsKolmogorovProcess` assumptions above, let $\alpha>0$ satisfy $\alpha p<q-1$. Then for $P$-almost every $\omega$, every integer $j$ admits $K\ge0$ and $N\in\mathbb N$ such that for dyadic rationals $s,t\in[j,j+1]$ with $|s-t|\le(1/2)^N$,
--
--   $$
--   |X(s,\omega)-X(t,\omega)|\le K|s-t|^\alpha.
--   $$
--
--   The constants may depend on the path and on the interval index $j$.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L271-L306 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, declaration `LevyStochCalc.Brownian.Continuity.kc_ae_interval_holder`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Continuity.kc_ae_interval_holder_408915f
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ j : ℤ, ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧
      ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
        (j : ℝ) ≤ s → s ≤ (j : ℝ) + 1 → (j : ℝ) ≤ t → t ≤ (j : ℝ) + 1 →
        |s - t| ≤ (1 / 2 : ℝ) ^ N → |X s ω - X t ω| ≤ K * |s - t| ^ α := by sorry
