-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_withDensity_apply_le_moment
-- name    : OAI.NoiselessRegression.withDensity_apply_le_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:28:34.570314+00:00
-- url     : https://prove2.me/theorems/73d119d6-64a7-4f47-bc61-94a3124dfd65
-- title:
--   Hölder bound for the mass of a set under a density with bounded $p$-th moment
-- statement:
--   Let $(X,\mathcal A)$ be a measurable space with a measure $\mu$, let $f:X\to[0,\infty]$ be measurable, let $p\in\mathbb R$ with $p>1$, and let $C\in[0,\infty]$ satisfy $\int_X f^{p}\,d\mu\le C$. Write $f\mu$ for the measure with density $f$ with respect to $\mu$, so that $(f\mu)(S)=\int_S f\,d\mu$ for measurable $S$. Then for every measurable set $S\subseteq X$,
--
--   $$
--   (f\mu)(S)\;\le\;C^{1/p}\,\mu(S)^{1-1/p}.
--   $$
--
--   Thus a $p$-th moment bound on a density yields a uniform Hölder-type modulus of absolute continuity: sets of small $\mu$-measure have small $f\mu$-measure, with exponent $1-1/p\in(0,1)$. It is the step that converts moment bounds on smoothed observation densities into bounds for individual sets.
--
--   **Formalization Note** All quantities lie in $[0,\infty]$ with Mathlib's conventions, for instance $\infty^{s}=\infty$ for $s>0$ and $0\cdot\infty=0$. No finiteness or $\sigma$-finiteness of $\mu$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Smoothing.lean#L149-L163

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem OAI.NoiselessRegression.withDensity_apply_le_moment (f : X → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∫⁻ x, f x ^ p ∂μ ≤ C) (S : Set X) (hS : MeasurableSet S) :
    μ.withDensity f S ≤ C^(1/p) * (μ S)^(1 - 1/p) := by sorry
