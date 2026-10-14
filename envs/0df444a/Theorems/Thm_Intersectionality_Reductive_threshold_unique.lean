-- Prove2me | Theorems.Thm_Intersectionality_Reductive_threshold_unique
-- name    : Intersectionality.Reductive.threshold_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:36.231185+00:00
-- url     : https://prove2.me/theorems/00c565c4-a6e5-4ef3-bf84-5e0b445d028e
-- title:
--   Appendix D — for p ∈ P the capacity threshold t(θ) with S(θ, t(θ)) = α exists and is unique
-- statement:
--   Work in the model of the Setting: $X \subset \mathbb{R}$ an interval, $n \ge 2$, $\alpha \in (0,1)$, and $Q$ a rich and commutative family of strictly increasing bijections of $X$. Let $p \in P$, $x_0 \in X$ and $\theta \in X^n$, and let $S(\theta, x^*)$ be the total acceptance rate of the nonintersectional policy $r_g(\cdot \mid \theta)$ with threshold $x^*$. Then there is exactly one threshold $x^* \in X$ with
--   $$S(\theta, x^*) = \alpha.$$
--
--   This defines the threshold $t(\theta)$ that meets the capacity constraint. It reduces the search for a reductive representative outcome to the $n$ equations $R_i(\theta, t(\theta)) = \alpha$ in $\theta$.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 25 (PDF 26), Appendix D, "Let t(θ) be the unique threshold"

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting

namespace Intersectionality.Reductive

/-- Appendix D, p. 25: for every `p ∈ P`, base point `x₀` and `θ ∈ Xⁿ` there is exactly one
threshold `x*` with `S(θ, x*) = α`. -/
theorem threshold_unique (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X)) (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∀ (p : Intersectionality.Generic.DistSpace X n) (x0 : ↥X) (θ : Fin n → ↥X),
      ∃! xs : ↥X, totalRate p.1 Q x0 θ xs = α := by sorry

end Intersectionality.Reductive
