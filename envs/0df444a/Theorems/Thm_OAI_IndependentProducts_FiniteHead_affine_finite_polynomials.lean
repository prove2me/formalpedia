-- Prove2me | Theorems.Thm_OAI_IndependentProducts_FiniteHead_affine_finite_polynomials
-- name    : OAI.IndependentProducts.FiniteHead.affine_finite_polynomials
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:51:09.66904+00:00
-- url     : https://prove2.me/theorems/a5166d5a-7479-445d-b357-e5aacd943846
-- title:
--   Affine lower bound for the midpoint gain between head and tail polynomials
-- statement:
--   **Setting.** Let $\mathcal V$ be the tree of finite sequences of positive integers with root $\varnothing$, prefix order $\preceq$, parent map $u\mapsto u^-$ and nonroot vertices $\mathcal E$. Let $\mu$ be a probability measure on $\mathbb R$ with finite second moment and mean $\int w\,d\mu(w)=1$, put $C_\mu=2\big(\int w^2\,d\mu(w)\big)^{1/2}$ and assume $C_\mu>0$. Let $P_\mu=\mu^{\otimes\mathcal E}$ on $\mathbb R^{\mathcal E}$, let $X_\mu$ be the closed linear span in $L^1(P_\mu)$ of the path products $\Pi_v(\omega)=\prod_{\varnothing\ne u\preceq v}\omega(u)$, with the $L^1$ norm $\|\cdot\|$, and let $\pi_v\in X_\mu$ be the vector of $\Pi_v$.
--
--   Let $T$ be a finite head (finite, prefix-closed, containing $\varnothing$) with boundary $\partial T=\{e\in\mathcal E:e\notin T,\ e^-\in T\}$. For $v\in\mathcal V$ let $\operatorname{anc}_T(v)$ be the last vertex of $T$ on the path to $v$ (that is, $v$ if $v\in T$, and otherwise the parent of the boundary vertex of $T$ that is a prefix of $v$), and let $\rho_T(v)=\pi_v-\pi_{\operatorname{anc}_T(v)}$.
--
--   Let $\iota,\kappa$ be finite sets, $i\mapsto e_i$ an injective map $\iota\to\partial T$, and $v:\kappa\to\mathcal V$, $j:\kappa\to\iota$, $a:\kappa\to\mathbb R$ maps with $e_{j(k)}\preceq v_k$ for every $k\in\kappa$. For coefficients $c:T\to\mathbb R$ consider the head polynomial and the tail polynomial
--   $$
--   x=\sum_{u\in T}c_u\,\pi_u,\qquad y=\sum_{k\in\kappa}a_k\,\rho_T(v_k).
--   $$
--
--   **Theorem.** Let $t\ge0$, $A\ge0$ and $D\in\mathbb R$, and assume the scalar estimate
--   $$
--   A\|\alpha\|_2-Dr\le\int_{\mathbb R^\iota}\max\Big(t\,\Big|\beta+\sum_{i\in\iota}\alpha_iw_i\Big|-r,\;0\Big)\,d\mu^{\otimes\iota}(w)
--   $$
--   for all $\alpha\in\mathbb R^\iota$, $\beta\in\mathbb R$ and $r\ge0$, where $\|\alpha\|_2=(\sum_i\alpha_i^2)^{1/2}$. Then
--
--   $$
--   \frac{A}{C_\mu}\,\|y\|-D\,\|x\|\;\le\;\frac{\|x+ty\|+\|x-ty\|}{2}-\|x\|.
--   $$
--
--   The right-hand side is the midpoint gain of $X_\mu$ at the center $x$ in the direction $y$. The theorem says that for perturbations built from tail vertices hanging below distinct exit vertices of a finite head, the gain grows at least linearly in $\|y\|$, up to a penalty proportional to $\|x\|$, as soon as the corresponding one-dimensional estimate holds for affine forms in independent copies of the multiplier. It is the finite-dimensional core of the lower bounds for the averaged asymptotic midpoint modulus of $X_\mu$; the scalar estimate is verified separately for concrete multiplier laws.
--
--   **Formalization Note** The vectors are `∑ v : T.vertices, c v • pathVector μ h₂ v` and `∑ k, a k • T.relativeVector μ h₂ (v k)` in `productSpan μ`, the right-hand side is `midpointGain t x y`, and the scalar estimate is phrased with `euclidSize` and `excess t r z = max (t * |z| - r) 0`. The index types $\iota,\kappa$ live in `Type`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/AffineBounds.lean#L90-L162

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

open OAI OAI.IndependentProducts OAI.IndependentProducts.FiniteHead
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uO uR uS uΛ uΩ uι
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)
variable (hmean : ∫ w : ℝ, w ∂μ = 1)
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)
variable (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ) (hv : ∀ k, (e (j k)).val.val <+: v k)

include hmean he hv in
theorem OAI.IndependentProducts.FiniteHead.affine_finite_polynomials (c : T.vertices → ℝ) (t A D : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ aa : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize aa - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, aa i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    (A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))) *
      ‖∑ k, a k • T.relativeVector μ h₂ (v k)‖ -
      D * ‖∑ v : T.vertices, c v • pathVector μ h₂ v‖ ≤
      midpointGain t (∑ v : T.vertices, c v • pathVector μ h₂ v)
        (∑ k, a k • T.relativeVector μ h₂ (v k)) := by sorry
