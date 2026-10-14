-- Prove2me | Theorems.Thm_Intersectionality_Reductive_lemma_1_b
-- name    : Intersectionality.Reductive.lemma_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:47.842904+00:00
-- url     : https://prove2.me/theorems/ae77c4a6-f6bb-40ce-a7b5-7149c4a5197d
-- title:
--   Lemma 1(b) — the function in Q mapping x to y is unique
-- statement:
--   Let $X \subset \mathbb{R}$ and let $Q$ be a rich and commutative family of strictly increasing bijections of $X$: for all $x, y \in X$ some $q \in Q$ satisfies $q(x) = y$, and $q \circ q' = q' \circ q$ for all $q, q' \in Q$. Then for all $x, y \in X$ and $q, q' \in Q$,
--   $$q(x) = y = q'(x) \implies q = q'.$$
--
--   This makes "the function in $Q$ mapping $x$ to $y$" well defined, and with it the parameterization $r(\cdot \mid \theta)$ of $Q$ used in Appendix D.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 22 (PDF 23), Lemma 1(b)

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting

namespace Intersectionality.Reductive

/-- Lemma 1(b), p. 22: for a rich and commutative family `Q` of increasing bijections of `X`, the
function in `Q` mapping `x` to `y` is unique. -/
theorem lemma_1_b (X : Set ℝ) (Q : Set (↥X → ↥X)) (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∀ x y : ↥X, ∀ q ∈ Q, ∀ q' ∈ Q, q x = y → q' x = y → q = q' := by sorry

end Intersectionality.Reductive
