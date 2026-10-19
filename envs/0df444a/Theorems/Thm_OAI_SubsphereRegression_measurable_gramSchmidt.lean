-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_measurable_gramSchmidt
-- name    : OAI.SubsphereRegression.measurable_gramSchmidt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:11:10.61893+00:00
-- url     : https://prove2.me/theorems/fc24a0da-a2a8-42a4-a1a5-c1fb7f36f3eb
-- title:
--   Measurability of the Gram–Schmidt vectors as functions of the input tuple
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $n\in\mathbb{N}$, and give the space $E^{n}$ of tuples $v=(v_0,\dots,v_{n-1})$ the product $\sigma$-algebra. The Gram–Schmidt vectors $u_0(v),\dots,u_{n-1}(v)$ are defined recursively by
--   $$u_j(v)=v_j-\sum_{i<j}\operatorname{proj}_{u_i(v)}(v_j),\qquad\operatorname{proj}_{u}(w)=\begin{cases}\dfrac{\langle u,w\rangle}{\|u\|^{2}}\,u, & u\ne0,\\ 0, & u=0,\end{cases}$$
--   where $\operatorname{proj}_u$ is the orthogonal projection onto the line $\mathbb{R}u$. No linear independence is assumed: for dependent tuples some $u_j(v)$ vanish. The theorem states that for every index $0\le j<n$ the map
--   $$E^{n}\to E,\qquad v\mapsto u_j(v),$$
--   is measurable.
--
--   The Gram–Schmidt map is discontinuous at degenerate tuples, so measurability does not follow from continuity. This lemma allows quantities built from Gram–Schmidt vectors, such as products of their lengths (which compute Gram determinants and distances to affine spans), to be integrated against product measures of random points.
--
--   **Formalization Note** The statement is about Mathlib's `gramSchmidt ℝ v j` for `v : Fin n → E`, which subtracts the orthogonal projections onto the lines spanned by the earlier Gram–Schmidt vectors; the projection onto the line spanned by $0$ is $0$, matching the case distinction above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gram.lean#L162-L179

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
variable [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.measurable_gramSchmidt (j : Fin n) :
    Measurable (fun v : Fin n → E => gramSchmidt ℝ v j) := by sorry
