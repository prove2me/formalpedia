-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_prod_null_set_bound
-- name    : OAI.SubsphereRegression.prod_null_set_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:29:53.11317+00:00
-- url     : https://prove2.me/theorems/b44b4b20-3faa-4703-8be3-6dd0e1edbc79
-- title:
--   Product measure of a set bounded by a uniform bound on its sections
-- statement:
--   Let $(X,\mathcal F,\mu)$ and $(Y,\mathcal G,\nu)$ be measure spaces with $\mu$ and $\nu$ s-finite (countable sums of finite measures), and let $\mu\otimes\nu$ be their product measure on $X\times Y$. Let $S\subseteq X\times Y$ be null-measurable for $\mu\otimes\nu$ (measurable up to a $\mu\otimes\nu$-null set), and let $c\in[0,\infty]$. For $y\in Y$ let $S^y=\{x\in X:(x,y)\in S\}$ be the section of $S$ at $y$. If
--   $$\mu(S^y)\le c\quad\text{for }\nu\text{-almost every }y\in Y,$$
--   then
--   $$(\mu\otimes\nu)(S)\le c\cdot\nu(Y).$$
--
--   This is the form of Fubini's theorem used to bound an averaged success probability: it suffices to bound the conditional probability for almost every value of the conditioning variable. Null-measurability is the natural hypothesis when $S$ is defined through functions that are only almost-everywhere measurable.
--
--   **Formalization Note** The sections need not be measurable; Lean evaluates $\mu$ on them as an outer measure. The hypotheses `SFinite μ` and `SFinite ν` come from the enclosing section.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Spheres.lean#L432-L447

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem OAI.SubsphereRegression.prod_null_set_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ y ∂ν, μ {x | (x,y) ∈ S} ≤ c) :
    (μ.prod ν) S ≤ c * ν univ := by sorry
