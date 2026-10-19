-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_withDensity_apply_le_moment
-- name    : OAI.SubsphereRegression.withDensity_apply_le_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:16:12.504993+00:00
-- url     : https://prove2.me/theorems/4945be5b-80f9-4848-9f02-9b0534977821
-- title:
--   Hölder bound for the mass of a set under an $L^p$-bounded density
-- statement:
--   Let $(X,\mathcal F)$ be a measurable space with an arbitrary measure $\mu$ (no finiteness is assumed). Let $f:X\to[0,\infty]$ be measurable, let $p>1$ be real, and let $C\in[0,\infty]$ satisfy $\int_Xf^p\,d\mu\le C$. Then, for every measurable set $S\subseteq X$, the measure $f\mu$ with density $f$ with respect to $\mu$ satisfies
--   $$(f\mu)(S)=\int_Sf\,d\mu\;\le\;C^{1/p}\,\mu(S)^{1-1/p}.$$
--
--   This turns a moment bound on a density into a set-wise bound: sets of small $\mu$-measure have small $f\mu$-measure, with an explicit exponent $1-1/p>0$. It is used with $p=n+1$ to pass from an $L^{n+1}$ bound on the density of an observation law to a bound on the probability of any set.
--
--   **Formalization Note** Real powers are taken in $[0,\infty]$, where $\infty^{s}=\infty$ and $0^{s}=0$ for $s>0$; the measure $f\mu$ is `μ.withDensity f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gaussian.lean#L374-L388

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem OAI.SubsphereRegression.withDensity_apply_le_moment (f : X → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∫⁻ x, f x ^ p ∂μ ≤ C) (S : Set X) (hS : MeasurableSet S) :
    μ.withDensity f S ≤ C^(1/p) * (μ S)^(1 - 1/p) := by sorry
