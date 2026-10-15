-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_measurable_gramSchmidt
-- name    : OAI.NoiselessRegression.measurable_gramSchmidt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:25:05.006906+00:00
-- url     : https://prove2.me/theorems/93022015-55b7-4a93-b5ad-7ece86f6c8e8
-- title:
--   Gram–Schmidt vectors depend measurably on the input family
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, and let $n\in\mathbb{N}$. For a family $v=(v_0,\dots,v_{n-1})\in E^{n}$ the Gram–Schmidt vectors $u_0(v),\dots,u_{n-1}(v)$ are defined recursively by
--   $$u_j(v)=v_j-\sum_{i<j}\frac{\langle u_i(v),v_j\rangle}{\|u_i(v)\|^{2}}\,u_i(v),$$
--   where a term with $u_i(v)=0$ is $0$; equivalently, $u_j(v)$ is $v_j$ minus its orthogonal projection onto the span of $v_0,\dots,v_{j-1}$. Equip $E^{n}$ with the product $\sigma$-algebra. Then for every index $j\in\{0,\dots,n-1\}$ the map
--   $$
--   E^{n}\to E,\qquad v\mapsto u_j(v)
--   $$
--   is measurable.
--
--   The Gram–Schmidt map is not continuous at linearly dependent families, so its measurability is not automatic. It is needed to integrate functions of Gram–Schmidt norms, such as inverse powers of the distances of independent random points to the affine span of the previous ones, against product measures.
--
--   **Formalization Note** The vectors are Mathlib's `gramSchmidt ℝ v j`, defined by subtracting the orthogonal projections onto the lines spanned by the earlier Gram–Schmidt vectors; the displayed formula is this definition with Lean's convention $x/0=0$. Indices range over `Fin n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Gram.lean#L165-L182

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
variable [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.measurable_gramSchmidt (j : Fin n) :
    Measurable (fun v : Fin n → E => gramSchmidt ℝ v j) := by sorry
