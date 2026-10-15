-- Prove2me | Theorems.Thm_OAI_IndependentProducts_norm_child_difference
-- name    : OAI.IndependentProducts.norm_child_difference
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:05:52.788697+00:00
-- url     : https://prove2.me/theorems/8b4902cf-ff3a-4797-812e-b2bdfcda35e3
-- title:
--   The $L^1$ distance from a path product to a child equals the mean absolute deviation of the multiplier
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb{R}$ with finite second moment $\int w^2\,d\mu(w)<\infty$, which is concentrated on the positive reals ($w>0$ for $\mu$-almost every $w$) and has mean $\int w\,d\mu(w)=1$. Put independent copies of $\mu$ on the nonroot vertices $\mathcal E$ of the tree $\mathcal V$ of finite sequences of positive integers, giving the product measure $\mu^{\otimes\mathcal E}$ on $\mathbb{R}^{\mathcal E}$. For $v=(v_1,\dots,v_m)\in\mathcal V$ the path product $\Pi_v(\omega)=\prod_{j=1}^{m}\omega_{(v_1,\dots,v_j)}$ is square integrable, and $[\Pi_v]$ denotes its class in the closed linear span $\mathcal X_\mu\subseteq L^1(\mu^{\otimes\mathcal E})$ of all path products, normed by the $L^1$ norm. For $n\in\mathbb{N}$ let $\mathrm{ch}_n(v)=(v_1,\dots,v_m,n+1)$.
--
--   For every vertex $v$ and every $n\in\mathbb{N}$,
--
--   $$\bigl\|[\Pi_{\mathrm{ch}_n(v)}]-[\Pi_v]\bigr\|_{L^1(\mu^{\otimes\mathcal E})}=\int_{\mathbb{R}}|w-1|\,d\mu(w).$$
--
--   Thus all branch increments of the tree of path products have the same size $\rho=\int|w-1|\,d\mu$, which is strictly positive unless $\mu$ is the point mass at $1$. This provides the constant-increment hypothesis of the tree obstruction to equivalent asymptotically uniformly convex norms on $\mathcal X_\mu$.
--
--   **Formalization Note** The finite second moment is the hypothesis `MemLp (fun w => w) 2 μ`, which is also what is needed to form the vector `pathVector μ h₂ v` in `productSpan μ`; positivity is an almost-everywhere statement for $\mu$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/PathMoments.lean#L256-L278

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

theorem OAI.IndependentProducts.norm_child_difference (h₂ : MemLp (fun w : ℝ => w) 2 μ)
    (hpos : ∀ᵐ w ∂μ, (0 : ℝ) < w) (hmean : ∫ w : ℝ, w ∂μ = 1) (v : Vertex) (n : ℕ) :
    ‖pathVector μ h₂ (child v n) - pathVector μ h₂ v‖ = ∫ w : ℝ, |w - 1| ∂μ := by sorry
