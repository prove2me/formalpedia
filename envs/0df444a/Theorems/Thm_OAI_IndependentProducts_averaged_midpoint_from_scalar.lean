-- Prove2me | Theorems.Thm_OAI_IndependentProducts_averaged_midpoint_from_scalar
-- name    : OAI.IndependentProducts.averaged_midpoint_from_scalar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:52:00.952796+00:00
-- url     : https://prove2.me/theorems/606d5877-68c0-4417-ab4f-4352b9b60a6c
-- title:
--   Scalar excess inequalities imply a lower bound for the averaged midpoint modulus of the $L^1$ product span
-- statement:
--   **Setting.** Let $\mathcal T$ be the tree of finite sequences of positive integers, with root the empty sequence $\varnothing$, and let $E=\mathcal T\setminus\{\varnothing\}$ be its set of nonroot vertices. For $v=(v_1,\dots,v_k)\in\mathcal T$ and $1\le j\le k$ write $v|_j=(v_1,\dots,v_j)$ for the prefix of length $j$. Let $\mu$ be a Borel measure on $\mathbb R$ satisfying the *multiplier hypotheses*: $\mu$ is a probability measure, $\mu$-almost every $w$ is positive, $\mu$ is not almost surely equal to any constant, $\int w\,d\mu(w)=1$, and $\int w^2\,d\mu(w)<\infty$. Put $m_2=\int w^2\,d\mu(w)$. On the sample space $\mathbb R^{E}$ let $\mathbb P_\mu=\mu^{\otimes E}$ be the product of independent copies of $\mu$, one for each nonroot vertex, and define the path products
--
--   $$
--   \pi_v(\omega)=\prod_{j=1}^{|v|}\omega(v|_j),\qquad \pi_\varnothing=1 .
--   $$
--
--   Let $X_\mu$ be the closure in $L^1(\mathbb P_\mu)$ of the linear span of the classes of the $\pi_v$, equipped with the $L^1$ norm. Its averaged asymptotic midpoint modulus at $t$ is
--
--   $$
--   \bar\delta_{X_\mu}(t)=\inf_{\|x\|=1}\ \sup_{F}\ \inf_{\substack{y\in F\\ \|y\|\ge 1}}\Big(\frac{\|x+ty\|+\|x-ty\|}{2}-1\Big),
--   $$
--
--   where $x$ ranges over unit vectors of $X_\mu$ and $F$ over the closed linear subspaces of $X_\mu$ of finite codimension. Finally let $\operatorname{exc}_{t,r}(z)=\max(t|z|-r,\,0)$ for real $t,r,z$, and $\|a\|_2=\big(\sum_i a_i^2\big)^{1/2}$.
--
--   **Theorem.** Let $t,A,D$ be real numbers with $t\ge 0$, $A\ge 0$, $D\ge 0$, and assume $2\sqrt{m_2}>0$. Suppose that for every finite index set $\iota$, every $a\in\mathbb R^\iota$, every $b\in\mathbb R$ and every $r\ge 0$,
--
--   $$
--   A\,\|a\|_2-D\,r\;\le\;\int_{\mathbb R^\iota}\operatorname{exc}_{t,r}\Big(b+\sum_{i\in\iota}a_i w_i\Big)\,d\mu^{\otimes\iota}(w).
--   $$
--
--   Then
--
--   $$
--   \frac{A}{2\sqrt{m_2}}-D\;\le\;\bar\delta_{X_\mu}(t).
--   $$
--
--   This is a transfer principle: a one-dimensional anti-concentration estimate for affine combinations of independent copies of the multiplier, uniform in the number of variables and in the shift $b$, yields a quantitative lower bound for the averaged midpoint modulus of the infinite-dimensional space $X_\mu$. The explicit bounds for exponential and squared-Gaussian multipliers are obtained by verifying the scalar hypothesis for those two laws.
--
--   **Formalization Note** The multiplier hypotheses are the structure `MultiplierHypotheses μ`, the space is `productSpan μ` with its own norm (`normSeminorm`), and the modulus is `averagedMidpointModulus`, built from real `sInf`/`sSup` over `CofiniteSubspaces` (closed submodules with finite-dimensional quotient). The index set $\iota$ ranges over finite types in `Type`, $\|a\|_2$ is `euclidSize`, and $\operatorname{exc}_{t,r}$ is `excess t r`. The hypothesis $2\sqrt{m_2}>0$ is stated explicitly, although it also follows from the mean-one condition, since $m_2\ge\big(\int w\,d\mu\big)^2=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/GaussianBounds.lean#L39-L64

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
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

theorem OAI.IndependentProducts.averaged_midpoint_from_scalar (μ : Measure ℝ) (hμ : MultiplierHypotheses μ)
    (t A D : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ (ι : Type) [Fintype ι], ∀ aa : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize aa - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, aa i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ)) - D ≤
      averagedMidpointModulus (productSpan μ) (normSeminorm ℝ (productSpan μ)) t := by sorry
