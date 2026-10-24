-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_level_bad_measure_408915f
-- name    : LevyStochCalc.Brownian.Continuity.kc_level_bad_measure_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:52:01.254405+00:00
-- url     : https://prove2.me/theorems/31c691a6-7600-4664-ad62-1778e545378d
-- title:
--   Dyadic-Level Bad-Set Measure Bound
-- statement:
--   This is the per-level bad-set estimate for a Kolmogorov process. Let $(\Omega,P)$ be a probability space, $X:\mathbb R\to\Omega\to\mathbb R$, $p,q\in\mathbb R$, $M\in\mathbb R_{\ge0}$, and assume `hX : IsKolmogorovProcess X P p q M`. For every $\alpha\in\mathbb R$ and $n\in\mathbb N$, the union over $k<2^n$ of the events
--
--   $$
--   \left\{\omega:\bigl((1/2)^\alpha\bigr)^n<\left|X\!\left(\frac{k+1}{2^n},\omega\right)-X\!\left(\frac{k}{2^n},\omega\right)\right|\right\}
--   $$
--
--   has measure at most
--
--   $$
--   \operatorname{ofReal}\!\left(M\bigl((1/2)^{q-\alpha p-1}\bigr)^n\right).
--   $$
--
--   The conclusion is an `ENNReal` inequality and does not assume $\alpha p<q-1$.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L94-L143 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, declaration `LevyStochCalc.Brownian.Continuity.kc_level_bad_measure`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Continuity.kc_level_bad_measure_408915f
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (n : ℕ) :
    P (⋃ k ∈ Finset.range (2 ^ n),
        {ω | ((1 / 2 : ℝ) ^ α) ^ n
            < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|})
      ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n) := by sorry
