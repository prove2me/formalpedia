-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kolmogorov_markov_bound_408915f
-- name    : LevyStochCalc.Brownian.Continuity.kolmogorov_markov_bound_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:51:58.851898+00:00
-- url     : https://prove2.me/theorems/48cad6c8-f150-4f9c-b9df-6f8a94c4fb40
-- title:
--   Kolmogorov Process Increment Tail Bound
-- statement:
--   This statement gives the Markov–Chebyshev tail estimate associated with a Kolmogorov process.
--
--   Let $\Omega$ be a measurable space, let $P$ be a probability measure on $\Omega$, and let $X : \mathbb{R} \to \Omega \to \mathbb{R}$ be a real-valued process. Let $p,q \in \mathbb{R}$ and $M \in [0,\infty)$, and assume the process satisfies `ProbabilityTheory.IsKolmogorovProcess X P p q M`. For arbitrary times $s,t \in \mathbb{R}$, let $\lambda \in [0,\infty]$ satisfy:
--
--   1. $0 < \lambda$;
--   2. $\lambda \ne \infty$.
--
--   Writing `edist` for the extended distance, the probability of an increment exceeding the threshold $\lambda$ is bounded by
--
--   $$
--   P\bigl(\{\omega \mid \lambda \le \operatorname{edist}(X(s,\omega),X(t,\omega))\}\bigr)
--   \le
--   \frac{M\,\operatorname{edist}(s,t)^q}{\lambda^p}.
--   $$
--
--   Here the right-hand side is interpreted in $[0,\infty]$, with $M$ coerced from $[0,\infty)$ to `ENNReal`; the powers are extended-real powers. This is a per-pair increment tail estimate that can be reused in convergence-in-measure and summability arguments for continuous modifications of stochastic processes.
--
--   **Formalization Note** The measure-valued quantity and all arithmetic in the conclusion use `ENNReal`; the hypotheses require the threshold to be strictly positive and not equal to `⊤`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L31-L75 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, declaration `LevyStochCalc.Brownian.Continuity.kolmogorov_markov_bound`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Continuity.kolmogorov_markov_bound_408915f
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (s t : ℝ) {lam : ℝ≥0∞} (hlam_pos : 0 < lam) (hlam_top : lam ≠ ⊤) :
    P {ω | lam ≤ edist (X s ω) (X t ω)}
      ≤ (M : ℝ≥0∞) * edist s t ^ q / lam ^ p := by sorry
