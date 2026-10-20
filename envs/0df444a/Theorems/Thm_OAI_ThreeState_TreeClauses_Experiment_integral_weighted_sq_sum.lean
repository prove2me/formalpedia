-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_integral_weighted_sq_sum
-- name    : OAI.ThreeState.TreeClauses.Experiment.integral_weighted_sq_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:07:14.267063+00:00
-- url     : https://prove2.me/theorems/be684672-769c-448b-8e29-65cc6bee36de
-- title:
--   Second moment of a sum under an independently tilted product measure
-- statement:
--   Let $(X,\mu)$ be a $\sigma$-finite measure space and $\iota$ a finite index set with $N=|\iota|$ elements. Let $a,u:X\to\mathbb{R}$ be such that $a$, $au$ and $au^2$ are $\mu$-integrable and $\int_Xa\,d\mu=1$. On $X^\iota$ with the product measure $\mu^{\otimes\iota}$, write $\Pi_a(x)=\prod_{j\in\iota}a(x_j)$. Then
--   $$
--   \int_{X^\iota}\Pi_a(x)\Bigl(\sum_{j\in\iota}u(x_j)\Bigr)^2d\mu^{\otimes\iota}(x)=N\int_Xa\,u^2\,d\mu+(N^2-N)\Bigl(\int_Xa\,u\,d\mu\Bigr)^2 .
--   $$
--
--   When $a\,d\mu$ is a probability measure, this is the familiar formula for the second moment of a sum of $N$ i.i.d. variables $U_j$: $\mathbb{E}\bigl(\sum_jU_j\bigr)^2=N\,\mathbb{E}U^2+N(N-1)(\mathbb{E}U)^2$. Here $a$ need not be nonnegative. The lemma is used to compute second moments of boundary statistics at a vertex with $N$ children.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/BranchMoments.lean#L197-L214

import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_BranchMoments

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Experiment
open scoped BigOperators ENNReal NNReal Topology
open Filter
open MeasureTheory
open scoped BigOperators
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
  {μ : Measure X} [SigmaFinite μ] {a u : X → ℝ}

theorem OAI.ThreeState.TreeClauses.Experiment.integral_weighted_sq_sum (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (hau₂ : Integrable (fun x ↦ a x*u x^2) μ) (hbal : ∫ x, a x ∂μ = 1) :
    (∫ x : ι → X, weightProduct a x*(∑ j, u (x j))^2 ∂(Measure.pi fun _ ↦ μ)) =
      (Fintype.card ι : ℝ)*(∫ x, a x*u x^2 ∂μ)+
      ((Fintype.card ι : ℝ)^2-(Fintype.card ι : ℝ))*(∫ x, a x*u x ∂μ)^2 := by sorry
