-- Prove2me | Theorems.Thm_OAI_IndependentProducts_FiniteHead_tailSpace_cofinite
-- name    : OAI.IndependentProducts.FiniteHead.tailSpace_cofinite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:46:17.047233+00:00
-- url     : https://prove2.me/theorems/1ae25355-398d-4675-8a46-6a7f65374abd
-- title:
--   The closed tail space of a finite head has finite codimension
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ with finite second moment. Let $\mathcal V$ be the tree of finite sequences of positive integers with root $\varnothing$, prefix order $\preceq$, parent map $u\mapsto u^-$ and nonroot vertices $\mathcal E$; let $P_\mu=\mu^{\otimes\mathcal E}$ on $\mathbb R^{\mathcal E}$, let $X_\mu$ be the closed linear span in $L^1(P_\mu)$ of the path products $\Pi_v(\omega)=\prod_{\varnothing\ne u\preceq v}\omega(u)$, and write $\pi_v\in X_\mu$ for the vector of $\Pi_v$. Let $T$ be a finite head, i.e. a finite set of vertices containing $\varnothing$ and closed under taking prefixes, with boundary $\partial T=\{e\in\mathcal E:e\notin T,\ e^-\in T\}$.
--
--   For $v\in\mathcal V$ let $\operatorname{anc}_T(v)$ be the last vertex of $T$ on the path to $v$: $\operatorname{anc}_T(v)=v$ if $v\in T$, and otherwise $\operatorname{anc}_T(v)=e^-$, where $e$ is the boundary vertex of $T$ that is a prefix of $v$. Put $\rho_T(v)=\pi_v-\pi_{\operatorname{anc}_T(v)}$ and define the tail space of $T$ as the closed linear span
--   $$
--   \mathcal T_T=\overline{\operatorname{span}}\{\rho_T(v):v\in\mathcal V\setminus T\}\subseteq X_\mu.
--   $$
--
--   **Theorem.** $\mathcal T_T$ is a closed subspace of finite codimension in $X_\mu$:
--
--   $$
--   \mathcal T_T\ \text{is closed and}\ \dim_{\mathbb R}\big(X_\mu/\mathcal T_T\big)<\infty.
--   $$
--
--   Tail spaces are the finite-codimensional subspaces used in the asymptotic midpoint moduli of $X_\mu$: the generators $\rho_T(v)$ record how a path product changes after the path has left $T$, while the finite-dimensional head span $\operatorname{span}\{\pi_u:u\in T\}$ accounts for the remaining finitely many dimensions.
--
--   **Formalization Note** The statement is `T.tailSpace μ h₂ ∈ CofiniteSubspaces (productSpan μ)`. The map $\operatorname{anc}_T$ is `T.ancestor`, which picks the boundary prefix with `Classical.choose` (it is unique).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ClosedTails.lean#L89-L100

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

open OAI OAI.IndependentProducts OAI.IndependentProducts.FiniteHead
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)
variable (T : FiniteHead)

theorem OAI.IndependentProducts.FiniteHead.tailSpace_cofinite : T.tailSpace μ h₂ ∈ CofiniteSubspaces (productSpan μ) := by sorry
