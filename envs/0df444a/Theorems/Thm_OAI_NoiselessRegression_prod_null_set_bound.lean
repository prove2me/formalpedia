-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_prod_null_set_bound
-- name    : OAI.NoiselessRegression.prod_null_set_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:45:35.465289+00:00
-- url     : https://prove2.me/theorems/cece7d67-a128-4a7a-87a6-4c0e26d4c19d
-- title:
--   Bounding the product measure of a set by almost-sure bounds on the measures of its sections
-- statement:
--   Let $(X,\mathcal X)$ and $(Y,\mathcal Y)$ be measurable spaces carrying s-finite measures $\mu$ on $X$ and $\nu$ on $Y$, and let $\mu\otimes\nu$ be the product measure on $X\times Y$. Let $S\subseteq X\times Y$ be null-measurable for $\mu\otimes\nu$, that is, $S$ differs from a measurable set by a subset of a $\mu\otimes\nu$-null set. For $y\in Y$ let $S^y=\{x\in X:(x,y)\in S\}$ be the section of $S$ at $y$. Let $c\in[0,\infty]$ and assume that $\mu(S^y)\le c$ for $\nu$-almost every $y\in Y$. Then
--
--   $$
--   (\mu\otimes\nu)(S)\le c\,\nu(Y).
--   $$
--
--   This is a Fubini-type averaging principle: a bound on the probability of a joint event, valid conditionally on almost every value of the second variable, transfers to the joint probability. It is used to fix the random samples or the internal randomness of a learner and to bound its success probability over the remaining randomness.
--
--   **Formalization Note** The hypothesis is stated with the measure of the possibly non-measurable section, i.e. the outer measure `μ {x | (x,y) ∈ S}`; arithmetic is in $[0,\infty]$ with $0\cdot\infty=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Rotational.lean#L31-L46

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere
import Definitions.Def_OAI_Probability_GaussianRegression_Stream
import Definitions.Def_OAI_Probability_GaussianRegression_Caps
import Definitions.Def_OAI_Probability_GaussianRegression_Execution
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem OAI.NoiselessRegression.prod_null_set_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ y ∂ν, μ {x | (x,y) ∈ S} ≤ c) :
    (μ.prod ν) S ≤ c * ν univ := by sorry
