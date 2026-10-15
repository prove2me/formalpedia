-- Prove2me | Theorems.Thm_OAI_IndependentProducts_averagedModulus_lower_of_approx
-- name    : OAI.IndependentProducts.averagedModulus_lower_of_approx
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:24:15.644411+00:00
-- url     : https://prove2.me/theorems/c1cd4472-3034-4be5-8744-98ff1340ad41
-- title:
--   Lower bounds for the averaged asymptotic midpoint modulus from approximate subspace estimates
-- statement:
--   Let $X$ be a real normed space that is not finite-dimensional. Write $\mathrm{Cof}(X)$ for the family of closed linear subspaces $F\subseteq X$ of finite codimension (that is, $X/F$ is finite-dimensional), and for $t\in\mathbb R$ and $x,y\in X$ write
--
--   $$
--   \Delta_t(x,y)=\frac{\|x+ty\|+\|x-ty\|}{2}-\|x\|
--   $$
--
--   for the midpoint gain. The averaged asymptotic midpoint modulus of $X$ at $t$ is
--
--   $$
--   \bar\delta_X(t)=\inf_{\|x\|=1}\ \sup_{F\in\mathrm{Cof}(X)}\ \inf_{y\in F,\ \|y\|\ge 1}\Big(\frac{\|x+ty\|+\|x-ty\|}{2}-1\Big)
--   $$
--
--   **Theorem.** Let $t,L\in\mathbb R$, and suppose that for every $x\in X$ with $\|x\|=1$ and every $\varepsilon>0$ there is $F\in\mathrm{Cof}(X)$ such that $\Delta_t(x,y)\ge L-\varepsilon$ for all $y\in F$ with $\|y\|\ge1$. Then
--
--   $$
--   L\le\bar\delta_X(t).
--   $$
--
--   This is the entry point for lower bounds on the averaged midpoint modulus: it suffices to produce, for each unit vector and each tolerance, a single finite-codimensional subspace on which the midpoint gain is almost $L$. The bookkeeping with the nested infima and suprema is done once and for all here.
--
--   **Formalization Note** The modulus is `averagedMidpointModulus X (normSeminorm ℝ X) t`, defined with the real `sInf` and `sSup`, which return $0$ on empty or unbounded sets; the infinite-dimensionality hypothesis is what guarantees that the sets involved are nonempty. No sign condition on $t$ is required.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/MidpointModulus.lean#L77-L127

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

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.IndependentProducts.averagedModulus_lower_of_approx (hdim : ¬ FiniteDimensional ℝ X) (t L : ℝ)
    (h : ∀ x : X, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ F ∈ CofiniteSubspaces X, ∀ y ∈ F, 1 ≤ ‖y‖ → L - ε ≤ midpointGain t x y) :
    L ≤ averagedMidpointModulus X (normSeminorm ℝ X) t := by sorry
