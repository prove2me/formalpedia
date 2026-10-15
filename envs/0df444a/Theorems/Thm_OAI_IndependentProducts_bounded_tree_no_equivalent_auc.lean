-- Prove2me | Theorems.Thm_OAI_IndependentProducts_bounded_tree_no_equivalent_auc
-- name    : OAI.IndependentProducts.bounded_tree_no_equivalent_auc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:59:12.246906+00:00
-- url     : https://prove2.me/theorems/9e9206e0-8415-4830-8a83-099730b93614
-- title:
--   A unit tree with weakly null branch increments of constant size rules out every equivalent AUC norm
-- statement:
--   Let $\mathcal V$ be the rooted tree of finite sequences of positive integers, with root $\varnothing$; for $v=(v_1,\dots,v_m)\in\mathcal V$ and $n\in\mathbb{N}=\{0,1,2,\dots\}$ let $\mathrm{ch}_n(v)=(v_1,\dots,v_m,n+1)$ denote its $(n+1)$-st child. Let $X$ be a real normed space and write $\operatorname{cof}(X)$ for the family of closed linear subspaces $F\subseteq X$ with finite-dimensional quotient $X/F$. A seminorm $N$ on $X$ is an *equivalent norm* if there are constants $0<a\le b$ with $a\|x\|\le N(x)\le b\|x\|$ for all $x\in X$, and it is *asymptotically uniformly convex* (AUC) if $\bar\delta_N(t)>0$ for every $t>0$, where
--
--   $$\bar\delta_N(t)=\inf_{x\in X,\ N(x)=1}\ \sup_{F\in\operatorname{cof}(X)}\ \inf_{y\in F,\ N(y)=1}\bigl(N(x+ty)-1\bigr).$$
--
--   **Theorem.** Let $P:\mathcal V\to X$ and $\rho>0$ be such that for all $v\in\mathcal V$ and $n\in\mathbb{N}$:
--
--   1. $\|P(v)\|=1$;
--   2. $\|P(\mathrm{ch}_n(v))-P(v)\|=\rho$;
--   3. the sequence $\bigl(P(\mathrm{ch}_n(v))-P(v)\bigr)_{n\in\mathbb{N}}$ is weakly null, i.e. $f\bigl(P(\mathrm{ch}_n(v))-P(v)\bigr)\to0$ as $n\to\infty$ for every continuous linear functional $f$ on $X$.
--
--   Then no equivalent norm on $X$ is AUC: for every seminorm $N$ on $X$,
--
--   $$N\ \text{is an equivalent norm}\qquad\Longrightarrow\qquad \bar\delta_N(t)\le0\ \text{ for some }t>0 .$$
--
--   This is the deterministic obstruction behind the non-renormability results for closed spans of independent products: the hypotheses concern only the tree $P$ in the original norm, while the conclusion excludes every equivalent renorming. In the application $P(v)$ is the path product at the vertex $v$ in the closed $L^1$ span, which has norm $1$, and the increments are the child jumps.
--
--   **Formalization Note** Infima and suprema are Lean's `sInf` and `sSup` on $\mathbb{R}$ (value $0$ on empty or unbounded sets). Equivalent norms are represented as seminorms with two-sided bounds (`IsEquivalentNorm X N`), AUC is `IsAUC X N`, the child is `child v n`, and weak nullity is `WeaklyNull`; completeness of $X$ is not assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/TreeObstruction.lean#L162-L239

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.IndependentProducts.bounded_tree_no_equivalent_auc (P : Vertex → X) (hP : ∀ v, ‖P v‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsize : ∀ v n, ‖P (child v n) - P v‖ = ρ)
    (hweak : ∀ v, WeaklyNull (fun n => P (child v n) - P v)) :
    ∀ N : Seminorm ℝ X, IsEquivalentNorm X N → ¬ IsAUC X N := by sorry
