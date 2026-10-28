-- Prove2me | Theorems.Thm_Intersectionality_Reductive_param_continuous
-- name    : Intersectionality.Reductive.param_continuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:55.831989+00:00
-- url     : https://prove2.me/theorems/6fdac4ff-7694-4f35-a7f5-09f00e75f06c
-- title:
--   Appendix D — r(x|θ) is continuous in θ
-- statement:
--   Let $X \subset \mathbb{R}$ be an interval and $Q$ a rich and commutative family of strictly increasing bijections of $X$. Fix $x_0 \in X$ and, for $\theta \in X$, let $r(\cdot \mid \theta)$ be the function $q \in Q$ with $q(x_0) = \theta$. Then for every $x \in X$ the map
--   $$\theta \longmapsto r(x \mid \theta), \qquad X \to X,$$
--   is continuous.
--
--   Continuity of the parameterization is what makes the acceptance rates $R_i(\theta, x^*)$ continuous in $\theta$, which the Poincaré–Miranda argument of Appendix D needs.
--
--   **Formalization Note.** $r(\cdot \mid \theta)$ is the chosen element of $Q$ sending $x_0$ to $\theta$ (unique by Lemma 1(b)). Continuity is for the subspace topology on $X$.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 24 (PDF 25), Appendix D, "Using Lemma 1, it is straightforward to prove"

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting

namespace Intersectionality.Reductive

/-- Appendix D, p. 24: with `r(· | θ)` the function `q ∈ Q` with `q(x₀) = θ`, `r(x | θ)` is
continuous in `θ` for all `x`. -/
theorem param_continuous (X : Set ℝ) (hX : X.OrdConnected) (Q : Set (↥X → ↥X))
    (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∀ x0 x : ↥X, Continuous (fun θ : ↥X => param Q x0 θ x) := by sorry

end Intersectionality.Reductive
