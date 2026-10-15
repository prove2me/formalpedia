-- Prove2me | Theorems.Thm_OAI_IndependentProducts_oneSided_pos_subspace
-- name    : OAI.IndependentProducts.oneSided_pos_subspace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:56:09.160562+00:00
-- url     : https://prove2.me/theorems/9e580eb2-be43-4ea9-b052-79df78c32098
-- title:
--   A positive one-sided asymptotic modulus gives a uniform gain on some finite-codimensional subspace
-- statement:
--   Let $X$ be a real normed space and $N$ a seminorm on $X$. Write $\operatorname{cof}(X)$ for the family of linear subspaces $F\subseteq X$ that are closed in the norm topology of $X$ and have finite-dimensional quotient $X/F$. For $t\in\mathbb{R}$ the one-sided asymptotic modulus of $N$ is
--
--   $$\bar\delta_N(t)=\inf_{x\in X,\ N(x)=1}\ \sup_{F\in\operatorname{cof}(X)}\ \inf_{y\in F,\ N(y)=1}\bigl(N(x+ty)-1\bigr).$$
--
--   **Theorem.** Let $t\in\mathbb{R}$ with $\bar\delta_N(t)>0$, and let $x\in X$ with $N(x)=1$. Then there exists $F\in\operatorname{cof}(X)$ such that
--
--   $$N(x+ty)\ \ge\ 1+\frac{\bar\delta_N(t)}{2}\qquad\text{for every }y\in F\text{ with }N(y)=1 .$$
--
--   In words, positivity of the inf-sup-inf modulus means that every $N$-unit vector is pushed outward by a definite amount, uniformly over all $N$-unit directions in some closed finite-codimensional subspace; the factor $\tfrac12$ leaves room to replace the supremum and the infimum by an actual subspace and actual vectors. This is the entry point of the argument showing that a tree with weakly null branch increments admits no equivalent asymptotically uniformly convex norm.
--
--   **Formalization Note** The infima and suprema are Lean's `sInf` and `sSup` on $\mathbb{R}$, which return $0$ for the empty set and for sets that are unbounded in the relevant direction; the hypothesis $\bar\delta_N(t)>0$ is therefore what guarantees that the outer infimum is a genuine one. No sign condition on $t$ is imposed. The modulus is `oneSidedModulus X N t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/TreeObstruction.lean#L58-L89

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.IndependentProducts.oneSided_pos_subspace (N : Seminorm ℝ X) {t : ℝ}
    (hδ : 0 < oneSidedModulus X N t) {x : X} (hx : N x = 1) :
    ∃ F ∈ CofiniteSubspaces X, ∀ y ∈ F, N y = 1 →
      1 + oneSidedModulus X N t / 2 ≤ N (x + t • y) := by sorry
