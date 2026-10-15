-- Prove2me | Theorems.Thm_OAI_IndependentProducts_dense_pathVector_span
-- name    : OAI.IndependentProducts.dense_pathVector_span
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:44:55.50992+00:00
-- url     : https://prove2.me/theorems/3960b709-0f1f-4555-af0d-6a0a525ea79b
-- title:
--   Path products span a dense subspace of the closed $L^1$ product span
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ with finite second moment. On the tree $\mathcal V$ of finite sequences of positive integers, with nonroot vertices $\mathcal E$, let $P_\mu=\mu^{\otimes\mathcal E}$ be the product measure on $\mathbb R^{\mathcal E}$, and let $\Pi_v(\omega)=\prod_{j=1}^{n}\omega\big((v_1,\dots,v_j)\big)$ be the path product of $v=(v_1,\dots,v_n)$ (with $\Pi_\varnothing=1$ for the root). Let $X_\mu$ be the closure in $L^1(P_\mu)$ of the real linear span of the classes of the path products, a Banach space in the $L^1$ norm. Since $\mu$ has a finite second moment, each $\Pi_v$ is square integrable, hence integrable, and defines a vector $\pi_v\in X_\mu$.
--
--   **Theorem.** The linear span of the path vectors is dense in $X_\mu$:
--
--   $$
--   \overline{\operatorname{span}_{\mathbb R}\{\pi_v:v\in\mathcal V\}}=X_\mu,
--   $$
--
--   the closure being taken in $X_\mu$.
--
--   While $X_\mu$ is defined as a closure inside $L^1(P_\mu)$, this statement is intrinsic to $X_\mu$ regarded as a normed space in its own right. It provides the dense set of finite linear combinations of path products on which midpoint-gain estimates are verified, and it shows that a closed subspace of $X_\mu$ containing all path vectors is all of $X_\mu$.
--
--   **Formalization Note** $X_\mu$ is `productSpan μ`, a `Submodule` of `Lp ℝ 1 (productMeasure μ)` with the subspace topology, and $\pi_v$ is `pathVector μ h₂ v`, where `h₂` is the finite-second-moment hypothesis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ClosedTails.lean#L25-L41

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)

theorem OAI.IndependentProducts.dense_pathVector_span :
    Dense ((Submodule.span ℝ (Set.range (pathVector μ h₂))) : Set (productSpan μ)) := by sorry
