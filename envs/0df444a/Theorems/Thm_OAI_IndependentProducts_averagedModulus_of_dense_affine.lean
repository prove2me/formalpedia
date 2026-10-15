-- Prove2me | Theorems.Thm_OAI_IndependentProducts_averagedModulus_of_dense_affine
-- name    : OAI.IndependentProducts.averagedModulus_of_dense_affine
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:26:50.066783+00:00
-- url     : https://prove2.me/theorems/e656e641-80a1-46d6-9b0e-7e4aeedd13e6
-- title:
--   Affine midpoint-gain bounds on a dense set bound the averaged midpoint modulus
-- statement:
--   Let $X$ be a real normed space that is not finite-dimensional, let $\mathrm{Cof}(X)$ be the family of closed linear subspaces of $X$ of finite codimension, let $\Delta_t(x,y)=\frac{\|x+ty\|+\|x-ty\|}{2}-\|x\|$ be the midpoint gain, and let
--
--   $$
--   \bar\delta_X(t)=\inf_{\|x\|=1}\ \sup_{F\in\mathrm{Cof}(X)}\ \inf_{y\in F,\ \|y\|\ge 1}\Big(\frac{\|x+ty\|+\|x-ty\|}{2}-1\Big)
--   $$
--
--   be the averaged asymptotic midpoint modulus of $X$ at $t$.
--
--   **Theorem.** Let $\mathcal D\subseteq X$ be dense and let $A,B,t\in\mathbb R$ with $A\ge0$ and $B\ge0$. Suppose that for every $u\in\mathcal D$ there is $F\in\mathrm{Cof}(X)$ such that
--
--   $$
--   A\|y\|-B\|u\|\le\Delta_t(u,y)\qquad\text{for all }y\in F.
--   $$
--
--   Then
--
--   $$
--   A-B\le\bar\delta_X(t).
--   $$
--
--   The criterion reduces asymptotic midpoint estimates to an affine lower bound for the midpoint gain, to be checked only at the points of a convenient dense set (for instance finite linear combinations of distinguished vectors) and for all vectors of some finite-codimensional subspace, with no normalization of $u$ or $y$: the gain must grow at rate $A$ in the size of the perturbation, at the cost of a penalty proportional to the size of the center.
--
--   **Formalization Note** The conclusion is `A - B ≤ averagedMidpointModulus X (normSeminorm ℝ X) t`; there is no sign condition on $t$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/MidpointModulus.lean#L129-L153

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

theorem OAI.IndependentProducts.averagedModulus_of_dense_affine (hdim : ¬ FiniteDimensional ℝ X)
    {D : Set X} (hD : Dense D) (A B t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ u ∈ D, ∃ F ∈ CofiniteSubspaces X,
      ∀ y ∈ F, A * ‖y‖ - B * ‖u‖ ≤ midpointGain t u y) :
    A - B ≤ averagedMidpointModulus X (normSeminorm ℝ X) t := by sorry
